import GQ2.GaloisCosetNorm
import GQ2.ResidueLift
import GQ2.TameTwoQuotient
import GQ2.UnitNormIndex
import GQ2.DimAssembly

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
  obtain ⟨y, hymem, hy0, hnorm⟩ :=
    exists_mem_fixedField_norm_pow (H := L.fixingSubgroup) (K := k.fixingSubgroup)
      ((InfiniteGalois.fixedField_fixingSubgroup L).symm ▸ hxL) hx0
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
    show ρ (ResidueLift.toAbs a * ResidueLift.toAbs b) ∈ S
    rw [map_mul]; exact mul_mem ha hb
  inv_mem' := fun {a} ha => by
    show ρ (ResidueLift.toAbs a)⁻¹ ∈ S
    rw [map_inv]; exact inv_mem ha

omit [DiscreteTopology C] [Finite C] in
theorem kerGal_le_preimGal (ρ : ContinuousMonoidHom AbsGalQ2 C) (S : Subgroup C) :
    ResidueLift.kerGal ρ ≤ preimGal ρ S := fun x hx => by
  show ρ (ResidueLift.toAbs x) ∈ S
  rw [show ρ (ResidueLift.toAbs x) = 1 from hx]
  exact one_mem S

omit [Finite C] in
theorem preimGal_isOpen (ρ : ContinuousMonoidHom AbsGalQ2 C) (S : Subgroup C) :
    IsOpen ((preimGal ρ S : Subgroup (Kummer.GaloisGroup ℚ_[2]))
      : Set (Kummer.GaloisGroup ℚ_[2])) :=
  (isOpen_discrete (S : Set C)).preimage ρ.continuous_toFun

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
  exact fun g hg => hx' g (kerGal_le_preimGal ρ (Subgroup.zpowers t) hg)

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
      map_one' := Subtype.ext (map_one ρ),
      map_mul' := fun a b =>
        Subtype.ext (map_mul ρ (ResidueLift.toAbs a.1) (ResidueLift.toAbs b.1)) } with hρ'
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
    exact ⟨fun h => congrArg Subtype.val h, fun h => Subtype.ext h⟩
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
    exact (Int.odd_mul.mp (hc ▸ (by exact_mod_cast hrodd : Odd (r : ℤ)))).1
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
    have := Int.odd_iff.mp hm_odd
    omega
  -- equal uniformizer norms, then half (A)
  have hπ : ‖FL.π‖ = ‖Fk.π‖ := by
    have h := relE_spec Fk FL hkL
    rw [hm1, zpow_one] at h
    exact h.symm
  exact hunram_of_uniformizer_norm_eq Fk FL hπ

end Assembly

/-! ## Increment 2 — the oddness input `hodd`

The remaining CFT/orientation half (design §2 steps 3–4): `Gal(F₀/ℚ₂)` is abelian, its
`ℤ₂`-unit image (c2c2's `card_unitImage_eq_e`: `#Gu = e_{F₀}`) dies in every finite `2`-group
quotient (the c2c3 factoring through `ν_t` + the B10′ orientation), and a subgroup of a finite
group with commuting elements that dies in the odd-torsion quotient has odd order — whence
`e_{F₀}` is odd. -/

/-! ### Descending a hom along a surjection -/

section Descend

variable {G C Q : Type*} [Group G] [Group C] [Group Q]

/-- Descend `ξ : G →* Q` along a surjection `ρ : G →* C` with `ker ρ ≤ ker ξ`. -/
noncomputable def descendHom (ρ : G →* C) (hρ : Function.Surjective ρ) (ξ : G →* Q)
    (hker : ρ.ker ≤ ξ.ker) : C →* Q where
  toFun c := ξ (Function.surjInv hρ c)
  map_one' := by
    have h1 : ξ (Function.surjInv hρ 1 * (1 : G)⁻¹) = 1 := hker (by
      rw [MonoidHom.mem_ker, map_mul, map_inv, Function.surjInv_eq hρ, map_one, mul_inv_cancel])
    rw [map_mul, map_inv, map_one, inv_one, mul_one] at h1
    exact h1
  map_mul' a b := by
    have hρab : ρ (Function.surjInv hρ (a * b)
        * (Function.surjInv hρ a * Function.surjInv hρ b)⁻¹) = 1 := by
      rw [map_mul, map_inv, map_mul, Function.surjInv_eq hρ, Function.surjInv_eq hρ,
        Function.surjInv_eq hρ, mul_inv_cancel]
    have h1 := hker (MonoidHom.mem_ker.mpr hρab)
    rw [MonoidHom.mem_ker, map_mul, map_inv, map_mul, mul_inv_eq_one] at h1
    exact h1

/-- The defining property: `descendHom ρ hρ ξ hker (ρ g) = ξ g`. -/
theorem descendHom_apply (ρ : G →* C) (hρ : Function.Surjective ρ) (ξ : G →* Q)
    (hker : ρ.ker ≤ ξ.ker) (g : G) : descendHom ρ hρ ξ hker (ρ g) = ξ g := by
  have h1 : ξ (Function.surjInv hρ (ρ g) * g⁻¹) = 1 := hker (by
    rw [MonoidHom.mem_ker, map_mul, map_inv, Function.surjInv_eq hρ, mul_inv_cancel])
  rw [map_mul, map_inv, mul_inv_eq_one] at h1
  exact h1

end Descend

/-! ### The odd-part machinery -/

section OddPart

variable {G : Type*} [Group G] [Finite G]

/-- A divisor of an odd number is odd. -/
theorem odd_of_dvd_odd {d n : ℕ} (h : d ∣ n) (hn : Odd n) : Odd d := hn.of_dvd_nat h

/-- The **odd-torsion subgroup** of a finite group whose elements commute: the elements of odd
order.  (Stated with the commutativity as a hypothesis `hab` rather than `[CommGroup G]`, matching
the `hab`-shape of `Gal(F₀/ℚ₂)` in the assembly.) -/
def oddTorsion (hab : ∀ a b : G, a * b = b * a) : Subgroup G where
  carrier := {g : G | Odd (orderOf g)}
  one_mem' := by simp [orderOf_one]
  mul_mem' := fun {a b} ha hb => by
    have hdvd : orderOf (a * b) ∣ Nat.lcm (orderOf a) (orderOf b) :=
      (Commute.orderOf_mul_dvd_lcm (hab a b))
    exact odd_of_dvd_odd (hdvd.trans (Nat.lcm_dvd_mul _ _)) (ha.mul hb)
  inv_mem' := fun {a} ha => by simpa [orderOf_inv] using ha

omit [Finite G] in
theorem oddTorsion_normal (hab : ∀ a b : G, a * b = b * a) : (oddTorsion hab).Normal :=
  ⟨fun n hn g => by rwa [hab g n, mul_assoc, mul_inv_cancel, mul_one]⟩

/-- The odd-torsion subgroup has odd order (Cauchy contrapositive: an even order would produce an
element of order `2` inside it). -/
theorem odd_card_oddTorsion (hab : ∀ a b : G, a * b = b * a) :
    Odd (Nat.card (oddTorsion hab)) := by
  by_contra hodd'
  have hev : Even (Nat.card (oddTorsion hab)) := Nat.not_odd_iff_even.mp hodd'
  haveI : Fintype ↥(oddTorsion hab) := Fintype.ofFinite _
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card (G := ↥(oddTorsion hab)) 2
    (by rw [← Nat.card_eq_fintype_card]; exact hev.two_dvd)
  have hcoe : orderOf ((x : G)) = 2 := by
    rw [← hx]
    exact orderOf_injective (oddTorsion hab).subtype Subtype.val_injective x
  have hodd : Odd (orderOf (x : G)) := x.2
  rw [hcoe] at hodd
  norm_num at hodd

/-- The quotient by the odd torsion is a `2`-group: `g^{2^a}` has odd order for
`a := (orderOf g).factorization 2`, so every class has `2`-power order. -/
theorem isPGroup_quotient_oddTorsion (hab : ∀ a b : G, a * b = b * a) :
    haveI := oddTorsion_normal hab
    IsPGroup 2 (G ⧸ oddTorsion hab) := by
  haveI := oddTorsion_normal hab
  rw [IsPGroup.iff_orderOf]
  intro q
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective q
  have hn0 : orderOf g ≠ 0 := (orderOf_pos g).ne'
  set a := (orderOf g).factorization 2 with ha
  have hdvd : orderOf (QuotientGroup.mk g : G ⧸ oddTorsion hab) ∣ 2 ^ a := by
    apply orderOf_dvd_of_pow_eq_one
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
    -- `g ^ 2^a` has odd order `ord_compl[2] (orderOf g)`
    show Odd (orderOf (g ^ 2 ^ a))
    have hgcd : Nat.gcd (orderOf g) (2 ^ a) = 2 ^ a :=
      Nat.gcd_eq_right (Nat.ordProj_dvd (orderOf g) 2)
    have hcompl : ¬ (2 ∣ orderOf g / 2 ^ a) := Nat.not_dvd_ordCompl Nat.prime_two hn0
    rw [orderOf_pow, hgcd]
    exact Nat.not_even_iff_odd.mp fun hev => hcompl hev.two_dvd
  obtain ⟨k, -, hEq⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
  exact ⟨k, hEq⟩

end OddPart

/-! ### The tame kill: reciprocity unit-images die in every finite 2-group through `C` -/

section TameKill

variable {C : Type} [Group C] [TopologicalSpace C] [DiscreteTopology C] [Finite C]

omit [Finite C] in
/-- **The tame kill** (design §2 step 4): any hom `ξ' : C →* Q` into a finite `2`-group kills
`ρ g` whenever `g` lifts a reciprocity unit-image.  `ξ' ∘ ρ = (ξ' ∘ c) ∘ B.tameF` (`hfac`)
with `ξ' ∘ c` continuous (`C` discrete), the orientation gives `ν_t (B.tameF g) = 1`, and the
c2c3 factoring `map_eq_one_of_nuT_eq_one_finite` kills it.  The topology on `Q` is irrelevant —
the discrete one is installed locally. -/
theorem unit_dies_in_two_group {Q : Type*} [Group Q] [Finite Q] (hQ2 : IsPGroup 2 Q)
    (R : LocalReciprocity) (B : BoundaryMaps) (c : ContinuousMonoidHom Ttame C)
    (ρ : ContinuousMonoidHom AbsGalQ2 C) (hfac : ∀ g, ρ g = c (B.tameF g))
    (horient : TameUnitOrientation R B.tameF)
    (ξ' : C →* Q) (u : ℤ_[2]ˣ) (g : AbsGalQ2) (hg : toAb g = R.recip (unitEmbed u)) :
    ξ' (ρ g) = 1 := by
  letI : TopologicalSpace Q := ⊥
  haveI : DiscreteTopology Q := ⟨rfl⟩
  have hcont : Continuous (⇑(ξ'.comp c.toMonoidHom)) := by
    show Continuous fun x : Ttame => ξ' (c x)
    exact Continuous.comp (continuous_of_discreteTopology (α := C)) c.continuous_toFun
  set φ : ContinuousMonoidHom Ttame Q := ⟨ξ'.comp c.toMonoidHom, hcont⟩ with hφ
  rw [hfac]
  exact map_eq_one_of_nuT_eq_one_finite hQ2 φ (horient u g hg)

end TameKill

/-! ### `e_{F₀}` is odd -/

section OddE

variable {C : Type} [Group C] [TopologicalSpace C] [DiscreteTopology C] [Finite C]

/-- **The oddness input** (design §2 steps 3–4 assembled): for the inertia-preimage field
`F₀ := ℚ̄₂^{ρ⁻¹⟨t⟩}` at `t := c tameTau`, the absolute ramification index `e_{F₀}` is **odd**.

`⟨t⟩ ◁ C` (`Tame.zpowers_normal_of_tame` on the pushed tame relation), so `F₀/ℚ₂` is Galois
(`InfiniteGalois.normal_iff_isGalois`); the restriction `G_ℚ₂ → Gal(F₀/ℚ₂)` descends along `ρ`
to a surjection `κ : C →* Gal(F₀/ℚ₂)` killing `⟨t⟩`, so `Gal(F₀/ℚ₂)` is a quotient of the
cyclic `C/⟨t⟩` — abelian.  c2c2's `card_unitImage_eq_e` counts the reciprocity unit-image as
`e_{F₀}`; the tame kill sends it into the odd-torsion subgroup, whose order is odd. -/
theorem odd_e_inertiaField (R : LocalReciprocity) (B : BoundaryMaps)
    (c : ContinuousMonoidHom Ttame C) (hc : Function.Surjective ⇑c)
    (ρ : ContinuousMonoidHom AbsGalQ2 C) (hfac : ∀ g, ρ g = c (B.tameF g))
    (horient : TameUnitOrientation R B.tameF)
    (F₀F : DyadicUnitFiltration (inertiaField ρ (c tameTau))) :
    Odd F₀F.e := by
  classical
  have hρsurj : Function.Surjective ⇑ρ := DimAssembly.rho_surjective B c hc ρ hfac
  have hgen : Subgroup.closure {c tameSigma, c tameTau} = ⊤ := DimAssembly.gen_of_surjective c hc
  have hrel : (c tameSigma)⁻¹ * c tameTau * c tameSigma = c tameTau ^ 2 :=
    DimAssembly.tame_rel_image c
  -- abstract `t := c tameTau` (keeping `hgen`/`hrel` in the generalized shape)
  revert F₀F
  generalize hteq : c tameTau = t at hgen hrel
  intro F₀F
  haveI : FiniteDimensional ℚ_[2] (inertiaField ρ t) := inertiaField_finiteDimensional ρ t
  -- `⟨t⟩ ◁ C`, hence the preimage is normal, hence `F₀/ℚ₂` is Galois
  haveI htN : (Subgroup.zpowers t).Normal := Tame.zpowers_normal_of_tame hgen hrel
  haveI hpreN : (preimGal ρ (Subgroup.zpowers t)).Normal := by
    refine ⟨fun n hn g => ?_⟩
    show ρ (ResidueLift.toAbs g * ResidueLift.toAbs n * (ResidueLift.toAbs g)⁻¹) ∈ Subgroup.zpowers t
    rw [map_mul, map_mul, map_inv]
    exact htN.conj_mem _ hn _
  haveI hGalF₀ : IsGalois ℚ_[2] (inertiaField ρ t) := by
    refine (InfiniteGalois.normal_iff_isGalois (inertiaField ρ t)).mp ?_
    rw [fixingSubgroup_inertiaField]
    exact hpreN
  -- the banked term-mode ker equality (`restrictHom` is defeq-opaque to `rw`)
  have hkerF : (restrictHom (inertiaField ρ t)).ker = (inertiaField ρ t).fixingSubgroup :=
    IntermediateField.restrictNormalHom_ker (inertiaField ρ t)
  -- the descended surjection `κ : C →* Gal(F₀/ℚ₂)` and its kill of `⟨t⟩`
  have hkerle : ρ.toMonoidHom.ker ≤ (restrictHom (inertiaField ρ t)).ker := by
    intro x hx
    rw [hkerF, fixingSubgroup_inertiaField]
    exact kerGal_le_preimGal ρ (Subgroup.zpowers t) hx
  set κ : C →* ((inertiaField ρ t) ≃ₐ[ℚ_[2]] (inertiaField ρ t)) :=
    descendHom ρ.toMonoidHom hρsurj (restrictHom (inertiaField ρ t)) hkerle with hκ
  have hκρ : ∀ g : AbsGalQ2, κ (ρ g) = restrictHom (inertiaField ρ t) g := fun g =>
    descendHom_apply ρ.toMonoidHom hρsurj (restrictHom (inertiaField ρ t)) hkerle g
  have hκsurj : Function.Surjective ⇑κ := by
    intro σ
    obtain ⟨g, hg⟩ := AlgEquiv.restrictNormalHom_surjective
      (F := ℚ_[2]) (K₁ := inertiaField ρ t) (E := AlgebraicClosure ℚ_[2]) σ
    exact ⟨ρ g, by rw [hκρ g]; exact hg⟩
  have hκt : κ t = 1 := by
    obtain ⟨gt, hgt⟩ := hρsurj t
    have hmem : gt ∈ (restrictHom (inertiaField ρ t)).ker := by
      rw [hkerF, fixingSubgroup_inertiaField]
      show ρ (ResidueLift.toAbs gt) ∈ Subgroup.zpowers t
      rw [show ρ (ResidueLift.toAbs gt) = t from hgt]
      exact Subgroup.mem_zpowers t
    have h1 : κ (ρ gt) = 1 := by rw [hκρ gt]; exact MonoidHom.mem_ker.mp hmem
    have h2 : κ t = κ (ρ gt) := by rw [hgt]
    rw [h2]
    exact h1
  -- `Gal(F₀/ℚ₂)` is abelian: `κ` factors through the cyclic `C ⧸ ⟨t⟩`
  have hab : ∀ σ τ : ((inertiaField ρ t) ≃ₐ[ℚ_[2]] (inertiaField ρ t)), σ * τ = τ * σ := by
    have hZle : Subgroup.zpowers t ≤ κ.ker :=
      Subgroup.zpowers_le.mpr (MonoidHom.mem_ker.mpr hκt)
    set κbar : C ⧸ Subgroup.zpowers t →* ((inertiaField ρ t) ≃ₐ[ℚ_[2]] (inertiaField ρ t)) :=
      QuotientGroup.lift (Subgroup.zpowers t) κ hZle with hκbar
    -- the quotient is generated by the class of `s₀ := c tameSigma`
    have hZtop : Subgroup.zpowers
        (QuotientGroup.mk (c tameSigma) : C ⧸ Subgroup.zpowers t) = ⊤ := by
      have h1 : (⊤ : Subgroup (C ⧸ Subgroup.zpowers t))
          = Subgroup.map (QuotientGroup.mk' (Subgroup.zpowers t)) ⊤ :=
        (Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective _)).symm
      rw [h1, ← hgen, MonoidHom.map_closure]
      have himg : (QuotientGroup.mk' (Subgroup.zpowers t)) '' {c tameSigma, t}
          = {QuotientGroup.mk (c tameSigma), 1} := by
        rw [Set.image_insert_eq, Set.image_singleton]
        congr 1
        rw [Set.singleton_eq_singleton_iff]
        exact (QuotientGroup.eq_one_iff _).mpr (Subgroup.mem_zpowers t)
      rw [himg, Set.insert_eq, Subgroup.closure_union, Subgroup.closure_singleton_one,
        ← Subgroup.zpowers_eq_closure, sup_bot_eq]
    intro σ τ
    obtain ⟨x, rfl⟩ := hκsurj σ
    obtain ⟨y, rfl⟩ := hκsurj τ
    have hx : κ x = κbar (QuotientGroup.mk x) := rfl
    have hy : κ y = κbar (QuotientGroup.mk y) := rfl
    obtain ⟨a, ha⟩ := Subgroup.mem_zpowers_iff.mp
      (hZtop ▸ Subgroup.mem_top (QuotientGroup.mk x : C ⧸ Subgroup.zpowers t))
    obtain ⟨b, hb⟩ := Subgroup.mem_zpowers_iff.mp
      (hZtop ▸ Subgroup.mem_top (QuotientGroup.mk y : C ⧸ Subgroup.zpowers t))
    rw [hx, hy, ← map_mul, ← map_mul, ← ha, ← hb, ← zpow_add, ← zpow_add, add_comm]
  -- the unit-image and its kill into the odd torsion
  haveI : Fintype ((inertiaField ρ t) ≃ₐ[ℚ_[2]] (inertiaField ρ t)) :=
    AlgEquiv.fintype ℚ_[2] (inertiaField ρ t)
  haveI hON : (oddTorsion hab).Normal := oddTorsion_normal hab
  have hGuO : (((restrictAb (inertiaField ρ t) hab).comp R.recip).comp unitEmbed).range
      ≤ oddTorsion hab := by
    rintro _ ⟨u, rfl⟩
    obtain ⟨g, hg⟩ := QuotientGroup.mk'_surjective commClosure (R.recip (unitEmbed u))
    have hg' : toAb g = R.recip (unitEmbed u) := hg
    have helt : (((restrictAb (inertiaField ρ t) hab).comp R.recip).comp unitEmbed) u
        = κ (ρ g) := by
      show restrictAb (inertiaField ρ t) hab (R.recip (unitEmbed u)) = κ (ρ g)
      rw [← hg', restrictAb_toAb, hκρ g]
    rw [helt, ← QuotientGroup.eq_one_iff
      (G := ((inertiaField ρ t) ≃ₐ[ℚ_[2]] (inertiaField ρ t))) (N := oddTorsion hab)]
    exact unit_dies_in_two_group (isPGroup_quotient_oddTorsion hab) R B c ρ hfac
      horient ((QuotientGroup.mk' (oddTorsion hab)).comp κ) u g hg'
  -- assemble the count
  have hodd_Gu : Odd (Nat.card
      (((restrictAb (inertiaField ρ t) hab).comp R.recip).comp unitEmbed).range) :=
    odd_of_dvd_odd (Subgroup.card_dvd_of_le hGuO) (odd_card_oddTorsion hab)
  have hcard := UnitNormIndex.card_unitImage_eq_e R (inertiaField ρ t) hab F₀F
  rwa [hcard] at hodd_Gu

end OddE

/-! ### The finale: the analytic `hunram` for the involution tower -/

section Finale

variable {C : Type} [Group C] [TopologicalSpace C] [DiscreteTopology C] [Finite C]

/-- **P-15f2c2c4, the deliverable**: the analytic `hunram` for c2b's involution tower — for
`k ≤ L` with fixing-index `2` and `L` the splitting field of `ρ` (`hLfix`), the norm value
groups of `L` and `k` agree, verbatim in the shape `ShapiroDeepness.hvanish_involution` and
`SectionSix.lemma_6_16` consume.

Composes the whole c2c chain: half (A) + increments 1–2 of this file + c2c1's `relE` kit +
c2c2's `card_unitImage_eq_e` + c2c3's factoring/orientation.  Parametric in
`R : LocalReciprocity` and the orientation `horient` (instantiated by the consumer at
`R := localReciprocity`, `horient := tameUnitOrientation_witness`-style at the axiom witness);
the B13 filtrations are taken from `dyadicUnitFiltration`.  **Ax: std-3 + B13** (B5/B10′ enter
only at the consumer's instantiation of `R`/`horient`). -/
theorem hunram_involution {k L : IntermediateField ℚ_[2] (AlgebraicClosure ℚ_[2])}
    [FiniteDimensional ℚ_[2] k] [FiniteDimensional ℚ_[2] L]
    (R : LocalReciprocity) (B : BoundaryMaps)
    (c : ContinuousMonoidHom Ttame C) (hc : Function.Surjective ⇑c)
    (ρ : ContinuousMonoidHom AbsGalQ2 C) (hfac : ∀ g, ρ g = c (B.tameF g))
    (horient : TameUnitOrientation R B.tameF)
    (hkL : k ≤ L)
    (hindex : ((L.fixingSubgroup).subgroupOf k.fixingSubgroup).index = 2)
    (hLfix : L.fixingSubgroup = ResidueLift.kerGal ρ) :
    ∀ x : AlgebraicClosure ℚ_[2], x ≠ 0 → x ∈ L →
      ∃ y : AlgebraicClosure ℚ_[2], y ≠ 0 ∧ y ∈ k ∧ ‖x‖ = ‖y‖ := by
  classical
  set t : C := c tameTau with ht
  set F₀ : IntermediateField ℚ_[2] (AlgebraicClosure ℚ_[2]) := inertiaField ρ t with hF₀
  haveI : FiniteDimensional ℚ_[2] F₀ := inertiaField_finiteDimensional ρ t
  have hρsurj : Function.Surjective ⇑ρ := DimAssembly.rho_surjective B c hc ρ hfac
  -- B13 filtrations
  set Fk : DyadicUnitFiltration k := dyadicUnitFiltration k with hFk
  set FL : DyadicUnitFiltration L := dyadicUnitFiltration L with hFL
  set F₀F : DyadicUnitFiltration F₀ := dyadicUnitFiltration F₀ with hF₀F
  -- the tower `F₀ ≤ L`
  have hF₀L : F₀ ≤ L := by
    have h1 := inertiaField_le ρ t
    rwa [← hLfix, InfiniteGalois.fixedField_fixingSubgroup L] at h1
  -- leg 1: `e(L/k) ∣ 2`
  have hm2 : relE Fk FL hkL ∣ 2 := relE_dvd_two Fk FL hkL hindex
  -- leg 2: `e(L/F₀) ∣ orderOf t`, an odd number
  have hcardpre : Nat.card (↥(preimGal ρ (Subgroup.zpowers t))
      ⧸ (ResidueLift.kerGal ρ).subgroupOf (preimGal ρ (Subgroup.zpowers t))) = orderOf t :=
    card_quot_preimGal ρ hρsurj t
  have hfinpre : Finite (↥(preimGal ρ (Subgroup.zpowers t))
      ⧸ (ResidueLift.kerGal ρ).subgroupOf (preimGal ρ (Subgroup.zpowers t))) := by
    refine (Nat.card_ne_zero.mp ?_).2
    rw [hcardpre]
    exact (orderOf_pos t).ne'
  have hfixquot : Finite (↥(F₀.fixingSubgroup)
      ⧸ (L.fixingSubgroup).subgroupOf F₀.fixingSubgroup) := by
    rw [hF₀, fixingSubgroup_inertiaField, hLfix]
    exact hfinpre
  have hdvd : relE F₀F FL hF₀L ∣ (orderOf t : ℤ) := by
    haveI := hfixquot
    have h := relE_dvd_of_index F₀F FL hF₀L
    have hcards : Nat.card (↥(F₀.fixingSubgroup)
        ⧸ (L.fixingSubgroup).subgroupOf F₀.fixingSubgroup) = orderOf t := by
      rw [hF₀, fixingSubgroup_inertiaField, hLfix]
      exact hcardpre
    rwa [hcards] at h
  have hrodd : Odd (orderOf t) :=
    Tame.tame_odd_order (orderOf_pos (c tameSigma)).ne' (DimAssembly.tame_rel_image c)
  -- leg 3: `e_{F₀}` odd (the CFT/orientation input)
  have hodd : Odd F₀F.e := odd_e_inertiaField R B c hc ρ hfac horient F₀F
  -- the assembly
  exact hunram_of_odd_eF0 Fk FL F₀F hkL hF₀L hm2 hrodd hdvd hodd

end Finale

end UnramifiedBridge

end GQ2
