import GQ2.GaloisCosetNorm
import GQ2.ResidueLift

/-!
# P-15f2c2c4 (N4): the `hunram` assembly — increment 1, the `e`-chain

The capstone of the analytic-`hunram` derivation (`docs/p15f2c2c-handoff.md` §2): for the
involution tower `k ≤ L` of c2b (`[L : k]`-fixing-index 2) the norm value groups agree,
`‖L^×‖ = ‖k^×‖`, in the verbatim shape `hvanish_involution` consumes.

**This increment** builds the complete arithmetic skeleton — everything except the
"`e_{F₀}` is odd" input (steps 3–4 of the derivation, gated on c2c2's CFT unit-index theorem +
the c2c3 factoring/orientation), which is threaded as the hypothesis `hodd`:

1. **the index-2 leg** (`relE_dvd_of_index`, instantiated at c2b's `hindex`): `m := e(L/k) ∣ 2`
   — c2c1's coset norm at the pair `L.fixingSubgroup ≤ k.fixingSubgroup`, memberships
   transported along the Galois correspondence `fixedField (fixingSubgroup ·) = ·`.
2. **the `⟨t⟩`-preimage leg**: `T₀ := ρ⁻¹⟨t⟩` (the `kerGal` two-views idiom), `F₀ :=
   fixedField T₀` finite-dimensional (open subgroup), `[T₀ : ker ρ] = orderOf t` (first
   isomorphism at the restricted `ρ`), whence `e(L/F₀) ∣ orderOf t` — **odd** by
   `Tame.tame_odd_order` at the instantiation.
3. **the assembly** (`hunram_of_odd_eF0`): `e_L = e(L/F₀)·e_{F₀}` odd [`hodd`], `e_L = m·e_k`,
   `m ∣ 2` ⟹ `m = 1` ⟹ `‖π_L‖ = ‖π_k‖` ⟹ half (A)'s `hunram_of_uniformizer_norm_eq`.

Axioms: everything here is **std-3** (B13 data threaded as `DyadicUnitFiltration` hypotheses,
the half-(A) idiom).  The increment-2 discharge of `hodd` will carry {B5, B10′} via
c2c2/c2c3; the final instantiation adds B13 at the `dyadicUnitFiltration` call sites.
-/

namespace GQ2

namespace UnramifiedBridge

open GaloisCosetNorm UnramifiedNorm IntermediateField

local notation "ℚ̄₂" => AlgebraicClosure ℚ_[2]

/-! ## Leg 1 — the index-2 pair: `relE (L/k) ∣ [k.fixingSubgroup : L.fixingSubgroup]` -/

section IndexLeg

variable {k L : IntermediateField ℚ_[2] ℚ̄₂}

/-- **`relE` divides the fixing-subgroup index** (leg 1, general form): for a tower `k ≤ L` of
finite-dimensional intermediate fields, the relative ramification index `e(L/k)` divides
`[k.fixingSubgroup : L.fixingSubgroup]`.  c2c1's coset-norm package at the subgroup pair,
with memberships transported along the Galois correspondence. -/
theorem relE_dvd_of_index [FiniteDimensional ℚ_[2] k] [FiniteDimensional ℚ_[2] L]
    (Fk : DyadicUnitFiltration k) (FL : DyadicUnitFiltration L) (hkL : k ≤ L)
    [Finite (↥(k.fixingSubgroup) ⧸ (L.fixingSubgroup).subgroupOf k.fixingSubgroup)] :
    relE Fk FL hkL
      ∣ (Nat.card (↥(k.fixingSubgroup) ⧸ (L.fixingSubgroup).subgroupOf k.fixingSubgroup) : ℤ) := by
  haveI : Fintype (↥(k.fixingSubgroup) ⧸ (L.fixingSubgroup).subgroupOf k.fixingSubgroup) :=
    Fintype.ofFinite _
  refine relE_dvd Fk FL hkL fun x hx0 hxL => ?_
  have hxF : x ∈ fixedField L.fixingSubgroup :=
    (InfiniteGalois.fixedField_fixingSubgroup L).symm ▸ hxL
  obtain ⟨y, hymem, hy0, hnorm⟩ :=
    exists_mem_fixedField_norm_pow (H := L.fixingSubgroup) (K := k.fixingSubgroup) hxF hx0
  exact ⟨y, hy0, (InfiniteGalois.fixedField_fixingSubgroup k) ▸ hymem, hnorm⟩

/-- Leg 1 at c2b's shape: the index-2 hypothesis gives `e(L/k) ∣ 2`. -/
theorem relE_dvd_two [FiniteDimensional ℚ_[2] k] [FiniteDimensional ℚ_[2] L]
    (Fk : DyadicUnitFiltration k) (FL : DyadicUnitFiltration L) (hkL : k ≤ L)
    (hindex : ((L.fixingSubgroup).subgroupOf k.fixingSubgroup).index = 2) :
    relE Fk FL hkL ∣ 2 := by
  haveI : Finite (↥(k.fixingSubgroup) ⧸ (L.fixingSubgroup).subgroupOf k.fixingSubgroup) := by
    refine (Nat.card_ne_zero.mp ?_).2
    show ((L.fixingSubgroup).subgroupOf k.fixingSubgroup).index ≠ 0
    omega
  have h := relE_dvd_of_index Fk FL hkL
  rwa [show Nat.card (↥(k.fixingSubgroup) ⧸ (L.fixingSubgroup).subgroupOf k.fixingSubgroup)
      = ((L.fixingSubgroup).subgroupOf k.fixingSubgroup).index from rfl, hindex] at h

end IndexLeg

/-! ## Leg 2 — the `⟨t⟩`-preimage: `T₀ := ρ⁻¹⟨t⟩`, `F₀ := fixedField T₀`, `[T₀ : ker ρ] = ord t` -/

section PreimLeg

variable {C : Type} [Group C] [TopologicalSpace C] [DiscreteTopology C] [Finite C]

/-- The `ρ`-preimage of a subgroup `S ≤ C`, repackaged as a subgroup of the `AlgEquiv`-view
Galois group (the `ResidueLift.kerGal` two-views idiom: the closure proofs cross the
`AbsGalQ2`/`Kummer.GaloisGroup` instance split by `exact`-level defeq). -/
def preimGal (ρ : ContinuousMonoidHom AbsGalQ2 C) (S : Subgroup C) :
    Subgroup (Kummer.GaloisGroup ℚ_[2]) where
  carrier := {x : Kummer.GaloisGroup ℚ_[2] | ρ (ResidueLift.toAbs x) ∈ S}
  one_mem' := by show ρ 1 ∈ S; rw [map_one]; exact one_mem S
  mul_mem' := fun {a b} ha hb => by
    show ρ (ResidueLift.toAbs (a * b)) ∈ S
    have hab : ResidueLift.toAbs (a * b) = ResidueLift.toAbs a * ResidueLift.toAbs b := rfl
    rw [hab, map_mul]
    exact mul_mem ha hb
  inv_mem' := fun {a} ha => by
    show ρ (ResidueLift.toAbs a⁻¹) ∈ S
    have hia : ResidueLift.toAbs a⁻¹ = (ResidueLift.toAbs a)⁻¹ := rfl
    rw [hia, map_inv]
    exact inv_mem ha

omit [DiscreteTopology C] [Finite C] in
theorem kerGal_le_preimGal (ρ : ContinuousMonoidHom AbsGalQ2 C) (S : Subgroup C) :
    ResidueLift.kerGal ρ ≤ preimGal ρ S := fun x hx => by
  show ρ (ResidueLift.toAbs x) ∈ S
  rw [show ρ (ResidueLift.toAbs x) = 1 from hx]
  exact one_mem S

omit [Finite C] in
theorem preimGal_isOpen (ρ : ContinuousMonoidHom AbsGalQ2 C) (S : Subgroup C) :
    IsOpen ((preimGal ρ S : Subgroup (Kummer.GaloisGroup ℚ_[2]))
      : Set (Kummer.GaloisGroup ℚ_[2])) := by
  have hcont : Continuous fun x : Kummer.GaloisGroup ℚ_[2] => ρ (ResidueLift.toAbs x) :=
    ρ.continuous_toFun
  have h1 : ((preimGal ρ S : Subgroup (Kummer.GaloisGroup ℚ_[2]))
      : Set (Kummer.GaloisGroup ℚ_[2]))
      = (fun x : Kummer.GaloisGroup ℚ_[2] => ρ (ResidueLift.toAbs x)) ⁻¹' (S : Set C) := rfl
  rw [h1]
  exact (isOpen_discrete (S : Set C)).preimage hcont

/-- The `⟨t⟩`-preimage field `F₀ := ℚ̄₂^{ρ⁻¹⟨t⟩}` — the fixed field of the preimage of the
inertia-image `⟨t⟩ ≤ C`. -/
noncomputable def inertiaField (ρ : ContinuousMonoidHom AbsGalQ2 C) (t : C) :
    IntermediateField ℚ_[2] ℚ̄₂ :=
  IntermediateField.fixedField (preimGal ρ (Subgroup.zpowers t))

omit [Finite C] in
/-- The closed-subgroup Galois correspondence recovers the preimage from its fixed field
(the `ResidueLift.fixingSubgroup_splitField` mirror). -/
theorem fixingSubgroup_inertiaField (ρ : ContinuousMonoidHom AbsGalQ2 C) (t : C) :
    (inertiaField ρ t).fixingSubgroup = preimGal ρ (Subgroup.zpowers t) :=
  InfiniteGalois.fixingSubgroup_fixedField
    ⟨preimGal ρ (Subgroup.zpowers t),
      Subgroup.isClosed_of_isOpen _ (preimGal_isOpen ρ (Subgroup.zpowers t))⟩

omit [Finite C] in
/-- `F₀` is finite over `ℚ₂` (its fixing subgroup is open). -/
theorem inertiaField_finiteDimensional (ρ : ContinuousMonoidHom AbsGalQ2 C) (t : C) :
    FiniteDimensional ℚ_[2] (inertiaField ρ t) := by
  refine (InfiniteGalois.isOpen_iff_finite (inertiaField ρ t)).mp ?_
  rw [fixingSubgroup_inertiaField]
  exact preimGal_isOpen ρ (Subgroup.zpowers t)

omit [DiscreteTopology C] [Finite C] in
/-- `F₀ ≤ L` for `L := fixedField (ker ρ)`: the fixed field is antitone in the subgroup. -/
theorem inertiaField_le (ρ : ContinuousMonoidHom AbsGalQ2 C) (t : C) :
    inertiaField ρ t ≤ IntermediateField.fixedField (ResidueLift.kerGal ρ) := by
  intro x hx
  have hx' : x ∈ IntermediateField.fixedField (preimGal ρ (Subgroup.zpowers t)) := hx
  rw [IntermediateField.mem_fixedField_iff] at hx' ⊢
  intro g hg
  exact hx' g (kerGal_le_preimGal ρ (Subgroup.zpowers t) hg)

omit [DiscreteTopology C] [Finite C] in
/-- **The quotient count of leg 2**: `[T₀ : ker ρ] = orderOf t` for surjective `ρ` — the first
isomorphism theorem at the restriction `T₀ → ⟨t⟩` of `ρ`. -/
theorem card_quot_preimGal (ρ : ContinuousMonoidHom AbsGalQ2 C)
    (hρsurj : Function.Surjective ρ) (t : C) :
    Nat.card (↥(preimGal ρ (Subgroup.zpowers t))
        ⧸ (ResidueLift.kerGal ρ).subgroupOf (preimGal ρ (Subgroup.zpowers t)))
      = orderOf t := by
  set T₀ := preimGal ρ (Subgroup.zpowers t) with hT₀
  -- the restricted map `T₀ →* ⟨t⟩`
  set ρ' : ↥T₀ →* ↥(Subgroup.zpowers t) :=
    { toFun := fun x => ⟨ρ (ResidueLift.toAbs x.1), x.2⟩,
      map_one' := by
        apply Subtype.ext
        show ρ (ResidueLift.toAbs 1) = 1
        exact map_one ρ,
      map_mul' := fun a b => by
        apply Subtype.ext
        show ρ (ResidueLift.toAbs (a.1 * b.1)) = ρ (ResidueLift.toAbs a.1) * ρ (ResidueLift.toAbs b.1)
        have hab : ResidueLift.toAbs (a.1 * b.1)
            = ResidueLift.toAbs a.1 * ResidueLift.toAbs b.1 := rfl
        rw [hab, map_mul] } with hρ'
  have hsurj : Function.Surjective ρ' := by
    rintro ⟨y, hy⟩
    obtain ⟨g, hg⟩ := hρsurj y
    have hgmem : (g : Kummer.GaloisGroup ℚ_[2]) ∈ T₀ := by
      show ρ (ResidueLift.toAbs g) ∈ Subgroup.zpowers t
      rw [show ρ (ResidueLift.toAbs g) = y from hg]
      exact hy
    exact ⟨⟨g, hgmem⟩, Subtype.ext hg⟩
  have hker : ρ'.ker = (ResidueLift.kerGal ρ).subgroupOf T₀ := by
    ext x
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    constructor
    · intro h
      exact congrArg Subtype.val h
    · intro h
      exact Subtype.ext h
  calc Nat.card (↥T₀ ⧸ (ResidueLift.kerGal ρ).subgroupOf T₀)
      = Nat.card (↥T₀ ⧸ ρ'.ker) := by rw [hker]
    _ = Nat.card ↥(Subgroup.zpowers t) :=
        Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective ρ' hsurj).toEquiv
    _ = orderOf t := Nat.card_zpowers t

end PreimLeg

/-! ## Leg 3 + assembly — the odd `e`-chain forces `m = 1`, whence `hunram` -/

section Assembly

variable {k L F₀ : IntermediateField ℚ_[2] ℚ̄₂}

/-- **The `e`-chain assembly** (P-15f2c2c4, modulo the c2c2/c2c3 oddness input): given
* the index-2 leg `e(L/k) ∣ 2`,
* the inertia leg `e(L/F₀) ∣ r` with `r` odd, and
* the CFT input `e_{F₀}` **odd** (`hodd` — c2c2's unit-index theorem + the c2c3
  factoring/orientation kill the even part; threaded here),

the tower `k ≤ L` has equal uniformizer norms, hence equal value groups — the analytic
`hunram`, verbatim in the shape `ShapiroDeepness.hvanish_involution` consumes.

Arithmetic: `e_L = e(L/F₀)·e_{F₀}` is odd (both factors odd — a divisor of an odd number is
odd); `e_L = e(L/k)·e_k` then forces `e(L/k)` odd; an odd positive divisor of `2` is `1`;
`relE_spec` at `1` gives `‖π_k‖ = ‖π_L‖`. -/
theorem hunram_of_odd_eF0
    [FiniteDimensional ℚ_[2] k] [FiniteDimensional ℚ_[2] L] [FiniteDimensional ℚ_[2] F₀]
    (Fk : DyadicUnitFiltration k) (FL : DyadicUnitFiltration L)
    (F₀F : DyadicUnitFiltration F₀)
    (hkL : k ≤ L) (hF₀L : F₀ ≤ L)
    (hm2 : relE Fk FL hkL ∣ 2)
    {r : ℕ} (hrodd : Odd r) (hdvd : relE F₀F FL hF₀L ∣ (r : ℤ))
    (hodd : Odd F₀F.e) :
    ∀ x : ℚ̄₂, x ≠ 0 → x ∈ L → ∃ y : ℚ̄₂, y ≠ 0 ∧ y ∈ k ∧ ‖x‖ = ‖y‖ := by
  -- `e(L/F₀)` is odd: it divides the odd `r`
  have hrelE₀_odd : Odd (relE F₀F FL hF₀L) := by
    obtain ⟨c, hc⟩ := hdvd
    have hrZ : Odd (r : ℤ) := by exact_mod_cast hrodd
    rw [hc] at hrZ
    exact (Int.odd_mul.mp hrZ).1
  -- `e_L` is odd: the tower product of two odds
  have heL_odd : Odd ((FL.e : ℤ)) := by
    rw [e_eq_relE_mul F₀F FL hF₀L]
    exact hrelE₀_odd.mul (by exact_mod_cast hodd)
  -- hence `m := e(L/k)` is odd
  have hm_odd : Odd (relE Fk FL hkL) := by
    rw [e_eq_relE_mul Fk FL hkL] at heL_odd
    exact (Int.odd_mul.mp heL_odd).1
  -- an odd positive divisor of `2` is `1`
  have hm1 : relE Fk FL hkL = 1 := by
    have hle : relE Fk FL hkL ≤ 2 := Int.le_of_dvd (by norm_num) hm2
    have hge : 1 ≤ relE Fk FL hkL := relE_pos Fk FL hkL
    have hcases : relE Fk FL hkL = 1 ∨ relE Fk FL hkL = 2 := by omega
    rcases hcases with h1 | h2
    · exact h1
    · rw [Int.odd_iff, h2] at hm_odd
      norm_num at hm_odd
  -- equal uniformizer norms, then half (A)
  have hπ : ‖FL.π‖ = ‖Fk.π‖ := by
    have h := relE_spec Fk FL hkL
    rw [hm1, zpow_one] at h
    exact h.symm
  exact hunram_of_uniformizer_norm_eq Fk FL hπ

end Assembly

end UnramifiedBridge

end GQ2
