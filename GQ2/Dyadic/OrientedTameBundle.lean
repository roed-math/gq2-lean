/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Opus-4.8 and Fable-5
-/
module

public import GQ2.TameQuotient
public import GQ2.UnitFiltration
public import GQ2.ZtwoPowering
public import GQ2.Dyadic.TameQuotientK
public import GQ2.Dyadic.MarkedRecipBundle

@[expose] public section

/-!
# AX4: the oriented tame quotient of `G_K` at `q_K = 2^f` — structure and derived layer

The general-`K` form of B10′ (`GQ2/TameQuotient.lean`): a closed normal pro-`2` subgroup
`W ≤ G_K` (wild inertia) with `G_K / W ≅ T_{q_K}` at the residue cardinality
`q_K = 2^{FF.f}` of B13's unit filtration, whose unramified coordinate `ν_t` is oriented against
AX3's marked reciprocity at `K`.

**The axiom itself is not here.**  `GQ2.orientedTameQuotientAt`, asserting an instance for every
finite `K/ℚ₂` and every `FF : DyadicUnitFiltration K`, lands separately in
`GQ2/Foundations/Axioms.lean` at the census flip (census 10 → 11, an orchestrator commit;
`docs/dyadic/ax4-proposal.md` §2.4, §6).  Everything in this file quantifies over an **arbitrary**
`R : LocalReciprocity` and an arbitrary `B : MarkedRecip R K` and `T : OrientedTameQuotientK B FF`,
so the file is axiom-free (`#print axioms` = the standard three) and sits *below* the axiom file
that will import it — the same discipline as AX3's bundle file
(`GQ2/Dyadic/MarkedRecipBundle.lean`) and B10′'s.

## What is here

* §1 — `qOf`, `uniformizerK`: the residue cardinality `q_K = 2^f` and B13's uniformizer as a unit
  of `K`, with the spectral spec that discharges AX3's `nu_ur_recip_uniformizer` (memo §2.2).
* §2 — the bundle `OrientedTameQuotientK` (memo §2.3): five clauses plus the `Normal`
  instance-binder.
* §3 — the derived layer (memo §2.5): `tameFK` with surjectivity and kernel, `O₂`-maximality
  (packet Lemma 3.3 at general `q`, i.e. F3's `o2_Tq_two_pow_eq_bot`), the packaged
  `LocalTameQuotientK`, uniqueness of `W`, the tame-reciprocity identity `ι ∘ ν_t ∘ tameF_K =
  ν_ur^K` and the boundary compatibility `ν_t ∘ tameF_K = ν₂ ∘ pro2F_K`, and
  `TameUnitOrientationK` in the packaging `GQ2/DetRamified.lean` consumes at `ℚ₂`.
* §4 — `f`-uniqueness for `DyadicUnitFiltration K` (memo §1.4) and the R2/R3 guard record.
* §5 — the `K = ⊥` regression (memo §3).
* §6 — the interim binder spellings of memo §5, restated as `abbrev`s, plus consumer-compatibility
  `example`s for the LG lane and the boundary lane.

## Conventions

Inherited verbatim: `rec` arithmetic and `ν` geometric (B5's house pair,
`GQ2/Reciprocity.lean`); the presented `σ ∈ T_q` is **geometric** Frobenius, since
`tame_relation_q` reads `σ⁻¹τσ = τ^q`, so `σ` is NSW (7.5.3)'s `σ⁻¹` — hence the uniformizer's
tame coordinate is `ztwoOne⁻¹`, not `ztwoOne` (memo §7 R1).  The `K`-side vocabulary
(`GalK`, `GalKab`, `toAbK`, `commClosureK`) is reused from AX3's bundle file, never re-derived
(memo §7 R6, the instance-path trap).

## Deviation: maximality is a theorem, not a clause

`W = O₂(G_K)` is **not** a field of the bundle — it is packet Lemma 3.3 at general `q`
(`tameDataK_maximal` below, from F3's `o2_Tq_two_pow_eq_bot`), exactly as B10 omits maximality and
`GQ2/Prop32.lean`'s `tameData_maximal` proves it at `q = 2` (memo §1.6, §7 R8).  Putting a proved
paper statement into the trust boundary is what the omission avoids.

## Duplication note

Two small generic bricks are restated here in the nested namespace `Aux` because the files that
carry them sit *above* `GQ2/Foundations/Axioms.lean` and so cannot be imported by a file the axiom
file must import: `Aux.isPGroup_map_of_isProP` (= `GQ2.SectionThree.isPGroup_map_of_isProP`,
`GQ2/Prop32.lean`) and `Aux.exists_norm_eq_zpow` (= `GQ2.UnramifiedNorm.norm_eq_zpow`,
`GQ2/UnramifiedNorm.lean`, whose core `exists_nat_val` lives in `GQ2/DeepCount/Bounds.lean`).
The names are kept distinct so both can be imported into the same environment; this is F3's
`TameQ`-namespace precedent.
-/

namespace GQ2.Dyadic

noncomputable section

local notation "ℚ̄₂" => AlgebraicClosure ℚ_[2]

/-! ## §0 Generic bricks re-proved below the axiom layer

See the module docstring's duplication note.  Nothing here is new mathematics. -/

namespace Aux

/-- **Restatement of `GQ2.SectionThree.isPGroup_map_of_isProP`** (`GQ2/Prop32.lean`): the image of
a pro-`2` subgroup in a discrete group is a `2`-group.  Needed for `tameDataK_maximal`; the
original lives above the axiom layer. -/
theorem isPGroup_map_of_isProP {P : Type*} [Group P] [TopologicalSpace P] {N : Subgroup P}
    (hN : IsProP 2 N) {G : Type*} [Group G] [TopologicalSpace G] [DiscreteTopology G]
    (f : P →* G) (hf : Continuous f) : IsPGroup 2 (N.map f) := by
  set f' : N →* G := f.comp N.subtype with hf'
  have hf'cont : Continuous f' := hf.comp continuous_subtype_val
  have hker_open : IsOpen ((f'.ker : Subgroup N) : Set N) := by
    rw [MonoidHom.coe_ker]
    exact (isOpen_discrete _).preimage hf'cont
  set U : OpenNormalSubgroup N := ⟨⟨f'.ker, hker_open⟩, inferInstance⟩ with hU
  have hp : IsPGroup 2 (N ⧸ U.toSubgroup) := hN U
  have hrange : IsPGroup 2 f'.range :=
    hp.of_surjective (QuotientGroup.rangeKerLift f') (QuotientGroup.rangeKerLift_surjective f')
  have heq : f'.range = N.map f := by
    rw [hf', MonoidHom.range_comp, Subgroup.subtype_range]
  rwa [heq] at hrange

/-- **Restatement of `GQ2.UnramifiedNorm.norm_eq_zpow`** (`GQ2/UnramifiedNorm.lean`), proved from
B13 discreteness alone: with a `DyadicUnitFiltration` uniformizer `π` for `k`, every nonzero
`x ∈ k` has norm an integer power of `‖π‖`.  For `‖x‖ ≤ 1` take the least `m` with
`‖π‖^{m+1} < ‖x‖` (then `x/π^m` is integral of norm `> ‖π‖`, hence of norm one by `hπ_max`); for
`‖x‖ > 1` apply that to `x⁻¹` and negate. -/
theorem exists_norm_eq_zpow {k : IntermediateField ℚ_[2] ℚ̄₂} (F : DyadicUnitFiltration k)
    {x : ℚ̄₂} (hx : x ∈ k) (hx0 : x ≠ 0) : ∃ n : ℤ, ‖x‖ = ‖F.π‖ ^ n := by
  have hnat : ∀ y : ℚ̄₂, y ∈ k → y ≠ 0 → ‖y‖ ≤ 1 → ∃ m : ℕ, ‖y‖ = ‖F.π‖ ^ m := by
    intro y hy hy0 hy1
    have hπpos : (0 : ℝ) < ‖F.π‖ := norm_pos_iff.mpr F.hπ_ne
    have hypos : (0 : ℝ) < ‖y‖ := norm_pos_iff.mpr hy0
    have hex : ∃ m : ℕ, ‖F.π‖ ^ (m + 1) < ‖y‖ := by
      obtain ⟨m, hm⟩ := exists_pow_lt_of_lt_one hypos F.hπ_lt
      exact ⟨m, lt_of_le_of_lt
        (pow_le_pow_of_le_one (norm_nonneg _) F.hπ_lt.le (Nat.le_succ m)) hm⟩
    classical
    refine ⟨Nat.find hex, ?_⟩
    have hfound : ‖F.π‖ ^ (Nat.find hex + 1) < ‖y‖ := Nat.find_spec hex
    have hupper : ‖y‖ ≤ ‖F.π‖ ^ Nat.find hex := by
      rcases Nat.eq_zero_or_pos (Nat.find hex) with h0 | hpos
      · rw [h0, pow_zero]; exact hy1
      · have hnot := Nat.find_min hex (Nat.sub_lt hpos one_pos)
        rw [not_lt] at hnot
        have harith : Nat.find hex - 1 + 1 = Nat.find hex := by omega
        rwa [harith] at hnot
    have hπmpos : (0 : ℝ) < ‖F.π‖ ^ Nat.find hex := pow_pos hπpos _
    have hle : ‖y / F.π ^ Nat.find hex‖ ≤ 1 := by
      rw [norm_div, norm_pow, div_le_one hπmpos]; exact hupper
    have hgt : ‖F.π‖ < ‖y / F.π ^ Nat.find hex‖ := by
      rw [norm_div, norm_pow, lt_div_iff₀ hπmpos, ← pow_succ']; exact hfound
    have heq : ‖y / F.π ^ Nat.find hex‖ = 1 := by
      by_contra hne
      exact absurd (F.hπ_max _ (div_mem hy (pow_mem F.hπ_mem _)) (lt_of_le_of_ne hle hne))
        (not_le.mpr hgt)
    calc ‖y‖ = ‖y / F.π ^ Nat.find hex‖ * ‖F.π‖ ^ Nat.find hex := by
          rw [norm_div, norm_pow, div_mul_cancel₀ _ (ne_of_gt hπmpos)]
      _ = ‖F.π‖ ^ Nat.find hex := by rw [heq, one_mul]
  rcases le_or_gt ‖x‖ 1 with h1 | h1
  · obtain ⟨m, hm⟩ := hnat x hx hx0 h1
    exact ⟨(m : ℤ), by rw [hm, zpow_natCast]⟩
  · have hnorm : ‖x⁻¹‖ ≤ 1 := by rw [norm_inv]; exact (inv_lt_one_of_one_lt₀ h1).le
    obtain ⟨m, hm⟩ := hnat x⁻¹ (k.inv_mem hx) (inv_ne_zero hx0) hnorm
    refine ⟨-(m : ℤ), ?_⟩
    rw [norm_inv] at hm
    rw [zpow_neg, zpow_natCast, ← hm, inv_inv]

end Aux

/-- **The seam `ι : Z₂ ≃ₜ* Multiplicative ℤ₂`** — `GQ2.ztwoEquivPadic` (`GQ2/ZtwoPowering.lean`)
re-typed at the `Ztwo` spelling.  `Ztwo` is *definitionally* `maxProPQuotient 2 Zhat`, but it is a
`def` into `ProfiniteGrp`, so the coercions only agree at `default` transparency; giving the seam a
name at the `Ztwo` type keeps every statement below elaborating at `instances` transparency.  This
is the same `ι` as `GQ2.SectionThree.prop_3_10_local_marked`'s. -/
def ztwoIota : ContinuousMulEquiv Ztwo (Multiplicative ℤ_[2]) := ztwoEquivPadic

/-- The generator pin of the seam: `ι(1) = ofAdd 1` (`GQ2.ztwoEquivPadic_ofInt_one`). -/
@[simp] theorem ztwoIota_ztwoOne : ztwoIota ztwoOne = Multiplicative.ofAdd (1 : ℤ_[2]) :=
  ztwoEquivPadic_ofInt_one

/-! ## §1 The residue cardinality and B13's uniformizer  (memo §2.2)

`q_K` is named through B13's unit filtration, not through a free `f` and not through F1's
`FieldParameters`: an unpinned `f` makes the axiom **inconsistent** (memo §7 R2 — `T_2^{ab} = Ẑ`
while `T_4^{ab} = Ẑ × ℤ/3`, so two instantiations would give `T_2 ≅ T_4` and hence `False`).
Owner answer Q2 confirms this parametrization. -/

section Vocabulary

variable (K : IntermediateField ℚ_[2] ℚ̄₂)

/-- **`q_K = 2^f`**, the residue cardinality read off B13's unit filtration (memo §1.4). -/
def qOf (FF : DyadicUnitFiltration K) : ℕ := 2 ^ FF.f

@[simp] theorem qOf_eq (FF : DyadicUnitFiltration K) : qOf K FF = 2 ^ FF.f := rfl

theorem two_le_qOf (FF : DyadicUnitFiltration K) : 2 ≤ qOf K FF := by
  calc (2 : ℕ) = 2 ^ 1 := (pow_one 2).symm
    _ ≤ 2 ^ FF.f := Nat.pow_le_pow_right (by norm_num) FF.hf_pos

theorem qOf_ne_zero (FF : DyadicUnitFiltration K) : qOf K FF ≠ 0 := by
  have := two_le_qOf K FF; omega

theorem even_qOf (FF : DyadicUnitFiltration K) : Even (qOf K FF) := by
  obtain ⟨f', hf'⟩ : ∃ f', FF.f = f' + 1 := ⟨FF.f - 1, by have := FF.hf_pos; omega⟩
  exact ⟨2 ^ f', by rw [qOf_eq, hf', pow_succ]; ring⟩

instance fact_two_le_qOf (FF : DyadicUnitFiltration K) : Fact (2 ≤ qOf K FF) :=
  ⟨two_le_qOf K FF⟩

/-- **B13's uniformizer as a unit of `K`.**  `FF.π` lies in `K` and is nonzero, and `(↥K)ˣ` is all
of `↥K ∖ {0}`, so this is a canonical element — which is why the bundle's uniformizer clause needs
no `∀`-with-spec form and cannot be vacuous (memo §7 R4). -/
def uniformizerK (FF : DyadicUnitFiltration K) : (↥K)ˣ :=
  Units.mk0 ⟨FF.π, FF.hπ_mem⟩ (fun h => FF.hπ_ne (congrArg Subtype.val h))

@[simp] theorem uniformizerK_coe (FF : DyadicUnitFiltration K) :
    ((uniformizerK K FF : ↥K) : ℚ̄₂) = FF.π := rfl

theorem norm_uniformizerK_lt_one (FF : DyadicUnitFiltration K) :
    ‖((uniformizerK K FF : ↥K) : ℚ̄₂)‖ < 1 := by
  rw [uniformizerK_coe]; exact FF.hπ_lt

/-- The maximality half of the B13 uniformizer spec, in the shape AX3's
`MarkedRecip.nu_ur_recip_uniformizer` takes it.  This is the **AX3 ↔ AX4 seam**: it is what lets
the two bundles' uniformizer clauses be matched (memo §1.8, §1.9). -/
theorem uniformizerK_max (FF : DyadicUnitFiltration K) :
    ∀ z : ↥K, z ≠ 0 → ‖(z : ℚ̄₂)‖ < 1 → ‖(z : ℚ̄₂)‖ ≤ ‖((uniformizerK K FF : ↥K) : ℚ̄₂)‖ := by
  intro z _ hz
  rw [uniformizerK_coe]
  exact FF.hπ_max _ z.2 hz

/-- Every unit of `K` is a norm-one unit times an integer power of B13's uniformizer — the
general-`K` replacement for `ℚ₂ˣ = ⟨2⟩ × ℤ₂ˣ` (memo §1.9; `Aux.exists_norm_eq_zpow` is the value
group input).  This is what makes tame reciprocity at `K` a *theorem*: clause `(b_K)` of AX3 and
the two orientation clauses of AX4 pin `ν` exactly on units and on `π`, and by this lemma that is
all of `Kˣ` up to the group law. -/
theorem exists_unit_zpow_decomp (FF : DyadicUnitFiltration K) (x : (↥K)ˣ) :
    ∃ (u : (↥K)ˣ) (n : ℤ), x = u * uniformizerK K FF ^ n ∧ ‖((u : ↥K) : ℚ̄₂)‖ = 1 := by
  obtain ⟨n, hn⟩ := Aux.exists_norm_eq_zpow FF (x : ↥K).2 (by simp)
  refine ⟨x * uniformizerK K FF ^ (-n), n, by rw [mul_assoc, ← zpow_add, neg_add_cancel,
    zpow_zero, mul_one], ?_⟩
  have hπ0 : ‖FF.π‖ ≠ 0 := norm_ne_zero_iff.mpr FF.hπ_ne
  have hval : ((((x * uniformizerK K FF ^ (-n) : (↥K)ˣ)) : ↥K) : ℚ̄₂)
      = ((x : ↥K) : ℚ̄₂) * FF.π ^ (-n) := by
    rw [Units.val_mul, Units.val_zpow_eq_zpow_val]
    push_cast
    simp only [uniformizerK, Units.val_mk0]
    exact congrArg (fun t => ((x : ↥K) : ℚ̄₂) * t) (map_zpow₀ K.val _ _)
  rw [hval, norm_mul, norm_zpow, hn, ← zpow_add₀ hπ0, add_neg_cancel, zpow_zero]

end Vocabulary

/-! ## §2 The bundle  (memo §2.3)

Five clauses and one `Prop`-carrying instance binder — strictly fewer than B10′'s six, because the
`∀`-spec uniformizer is replaced by the canonical `FF.π` and no generator clause is needed (the
field side is pinned by `ν`-compatibility alone; memo §0.1).

`K` and `R` are **implicit**, so the axiom's use-site reads `OrientedTameQuotientK (markedRecipAt K)
FF` exactly as memo §2.4 spells it. -/

/-- **The oriented tame quotient of `G_K` at `q_K = 2^f` (the general-`K` form of B10′).**
A closed normal pro-`2` subgroup `W ≤ G_K` (wild inertia, encoded intrinsically — Mathlib has no
ramification theory, the B10 deviation) with a continuous isomorphism `G_K / W ≅ T_{q_K}`,
`q_K = 2^{FF.f}` the residue cardinality of B13's unit filtration, whose unramified coordinate
`ν_t` is *compatible with AX3's marked reciprocity at `K`*: units land in `ker ν_t`, and the B13
uniformizer — `rec_K(π)` = *arithmetic* Frobenius — lands in the geometric-Frobenius coordinate
`ztwoOne⁻¹` (the presented `σ` is geometric: `tame_relation_q` reads `σ⁻¹τσ = τ^q`, so `σ` is
NSW (7.5.3)'s `σ⁻¹`).

Both orientation clauses read the value through an arbitrary lift `g` of the abelianized class
(well-posed: `ν_t ∘ equiv ∘ mk` kills `commClosureK` — continuous into an abelian `T2` target),
exactly as B10′ (`GQ2/TameQuotient.lean`).

**Maximality is not a field**: `W = O₂(G_K)` is packet Lemma 3.3 at general `q`
(`tameDataK_maximal` below, from F3's `o2_Tq_two_pow_eq_bot`; `GQ2/Prop32.lean`'s
`tameData_maximal` is the `q = 2` precedent), a theorem obligation, not an assertion.

Citation: **NSW [1], Ch. VII §7.5, Theorem (7.5.3) (Iwasawa)** with **(7.5.2)**, at base `K` with
residue cardinality `q_K`; Serre, *Local Fields* [7], Ch. IV (wild inertia is pro-`p`); Ch. XIII §4,
Proposition 13 and its corollary for the two orientation clauses.  Verification of the
general-`q`/general-`K` forms against the cited PDFs is **UNVERIFIED-pending-PDF**
(`docs/dyadic/ax4-proposal.md` §8 Q7): this docstring deliberately does not claim it.  The axiom
`GQ2.orientedTameQuotientAt` asserting an instance for every `(K, FF)` is **not** declared in this
file; it lands in `GQ2/Foundations/Axioms.lean` at the census flip (census 10 → 11). -/
structure OrientedTameQuotientK {K : IntermediateField ℚ_[2] ℚ̄₂} [FiniteDimensional ℚ_[2] K]
    {R : LocalReciprocity} (B : MarkedRecip R K) (FF : DyadicUnitFiltration K) where
  /-- The wild subgroup `W_K ≤ G_K`. -/
  W : Subgroup (GalK K)
  /-- `W_K` is normal. -/
  [normal : W.Normal]
  /-- `W_K` is closed. -/
  isClosed : IsClosed (W : Set (GalK K))
  /-- `W_K` is pro-`2`. -/
  isProP : IsProP 2 W
  /-- The tame quotient: `G_K / W_K ≅ T_{q_K}`, `q_K = 2^f` the residue cardinality. -/
  equiv : ContinuousMulEquiv (GalK K ⧸ W) (Tq (qOf K FF))
  /-- **Orientation, units.**  `ν_t(tame(rec_K u)) = 1` for every unit (`‖u‖ = 1`, the B11b
  idiom).  [Serre LF Ch. XIII §4, Prop. 13.] -/
  nuT_recip_unit : ∀ (u : (↥K)ˣ) (g : GalK K),
      ‖((u : ↥K) : ℚ̄₂)‖ = 1 →
      toAbK K g = B.recip u →
      nuTq (qOf K FF) (equiv (QuotientGroup.mk g)) = 1
  /-- **Orientation, uniformizer.**  `ν_t(tame(rec_K π)) = ztwoOne⁻¹` for B13's `π` (arithmetic
  Frobenius, geometric coordinate `−1`).  [ibid., corollary; B10′ pattern.] -/
  nuT_recip_uniformizer : ∀ g : GalK K,
      toAbK K g = B.recip (uniformizerK K FF) →
      nuTq (qOf K FF) (equiv (QuotientGroup.mk g)) = ztwoOne⁻¹

/-! ## §3 The derived layer  (memo §2.5)

Everything below takes `(B) (FF) (T : OrientedTameQuotientK B FF)`, so the file's axiom print stays
at the standard three.  The `ℚ₂` templates are `GQ2/BoundaryMapsWitness.lean` (`tameFHom`,
`ker_tameFHom`, `tameChar`, `tame_reciprocity`, `compatF_proved`), `GQ2/Prop32.lean`
(`tameData_maximal`), `GQ2/SectionThree.lean` (`LocalTameQuotient`) and
`GQ2/TameTwoQuotient.lean` (`TameUnitOrientation`). -/

section Derived

variable {K : IntermediateField ℚ_[2] ℚ̄₂} [FiniteDimensional ℚ_[2] K] {R : LocalReciprocity}
  {B : MarkedRecip R K} {FF : DyadicUnitFiltration K}

namespace OrientedTameQuotientK

/-- **`tameF_K : G_K ↠ T_{q_K}`**, the tame quotient map (`equiv ∘ mk`; the
`GQ2/BoundaryMapsWitness.lean` `tameFHom` template). -/
def tameFK (T : OrientedTameQuotientK B FF) : ContinuousMonoidHom (GalK K) (Tq (qOf K FF)) :=
  haveI := T.normal
  (⟨T.equiv.toMulEquiv.toMonoidHom, T.equiv.continuous_toFun⟩ :
    ContinuousMonoidHom (GalK K ⧸ T.W) (Tq (qOf K FF))).comp (quotientMk T.W)

@[simp] theorem tameFK_apply (T : OrientedTameQuotientK B FF) (g : GalK K) :
    T.tameFK g = T.equiv (QuotientGroup.mk g) := rfl

theorem tameFK_surjective (T : OrientedTameQuotientK B FF) : Function.Surjective T.tameFK :=
  haveI := T.normal
  T.equiv.surjective.comp (quotientMk_surjective T.W)

/-- `ker tameF_K = W_K`. -/
theorem ker_tameFK (T : OrientedTameQuotientK B FF) : T.tameFK.toMonoidHom.ker = T.W := by
  haveI := T.normal
  ext x
  rw [MonoidHom.mem_ker]
  constructor
  · intro h
    exact (QuotientGroup.eq_one_iff x).mp (T.equiv.injective (by rw [map_one]; exact h))
  · intro h
    show T.equiv (QuotientGroup.mk x) = 1
    rw [(QuotientGroup.eq_one_iff x).mpr h, map_one]

/-! ### `O₂`-maximality (memo §1.6): packet Lemma 3.3 at general `q`, **derived, never a clause** -/

/-- **`W_K = O₂(G_K)`, the containment half** — every closed normal pro-`2` subgroup of `G_K` lies
in `W_K`.  Its image in `T_{q_K}` is normal (surjectivity) and has `2`-group finite images
(`Aux.isPGroup_map_of_isProP`), hence is trivial by F3's `o2_Tq_eq_bot` = packet Lemma 3.3 at
general `q`; `q_K` is even because `f ≥ 1`.  The `q = 2` precedent is
`GQ2.SectionThree.tameData_maximal` (`GQ2/Prop32.lean`).

This is why maximality is **not** a field of the bundle (memo §7 R8): it is proved paper content,
and putting it in the axiom would enlarge the trust boundary for nothing. -/
theorem tameDataK_maximal (T : OrientedTameQuotientK B FF) :
    ∀ N : Subgroup (GalK K), N.Normal → IsClosed (N : Set (GalK K)) → IsProP 2 N → N ≤ T.W := by
  intro N hNn _ hNp
  haveI := T.normal
  set e : (GalK K ⧸ T.W) →* Tq (qOf K FF) := T.equiv.toMonoidHom with he
  set q : GalK K →* GalK K ⧸ T.W := QuotientGroup.mk' T.W with hq
  set M : Subgroup (Tq (qOf K FF)) := N.map (e.comp q) with hM
  have hesurj : Function.Surjective (e.comp q) := by
    rw [MonoidHom.coe_comp]
    exact T.equiv.surjective.comp (QuotientGroup.mk'_surjective _)
  haveI hMn : M.Normal := Subgroup.Normal.map hNn _ hesurj
  have hMbot : M = ⊥ := by
    refine o2_Tq_eq_bot (even_qOf K FF) M ?_
    intro G _ _ _ _ f hf
    rw [hM, Subgroup.map_map]
    refine Aux.isPGroup_map_of_isProP hNp _ ?_
    rw [MonoidHom.coe_comp, MonoidHom.coe_comp]
    exact (hf.comp T.equiv.continuous_toFun).comp continuous_quot_mk
  intro x hxN
  have h1 : e (q x) ∈ M := Subgroup.mem_map.mpr ⟨x, hxN, rfl⟩
  rw [hMbot, Subgroup.mem_bot] at h1
  exact (QuotientGroup.eq_one_iff x).mp (T.equiv.injective (by rw [map_one]; exact h1))

/-- **`W_K` is pinned uniquely by maximality**: any two AX4 bundles at `K` — over any marked
reciprocity data and any unit filtrations — have the same wild subgroup.  This is the intrinsic
form of the "canonical" of packet Prop. 3.4(1) on the field side, and it is what makes the
`K = ⊥` regression's `W_⊥ = W` a theorem (memo §1.10, §3 step 2). -/
theorem W_eq {R' : LocalReciprocity} {B' : MarkedRecip R' K} {FF' : DyadicUnitFiltration K}
    (T : OrientedTameQuotientK B FF) (T' : OrientedTameQuotientK B' FF') : T.W = T'.W :=
  le_antisymm (T'.tameDataK_maximal T.W T.normal T.isClosed T.isProP)
    (T.tameDataK_maximal T'.W T'.normal T'.isClosed T'.isProP)

end OrientedTameQuotientK

/-- **Packet Prop. 3.4(1), field side, bundled** — the AX4 bundle together with Lemma 3.3's
maximality, which pins `W_K` uniquely.  The `GQ2/SectionThree.lean` `LocalTameQuotient` template at
general `K`; the `maximal` field is *proved* (`OrientedTameQuotientK.tameDataK_maximal`), never
asserted, exactly as at `ℚ₂`. -/
structure LocalTameQuotientK {K : IntermediateField ℚ_[2] ℚ̄₂} [FiniteDimensional ℚ_[2] K]
    {R : LocalReciprocity} (B : MarkedRecip R K) (FF : DyadicUnitFiltration K)
    extends OrientedTameQuotientK B FF where
  /-- `W_K` is the **maximal** closed normal pro-`2` subgroup — packet Lemma 3.3's `O₂(G_K) = W_K`
  at general `q`. -/
  maximal : ∀ N : Subgroup (GalK K), N.Normal → IsClosed (N : Set (GalK K)) → IsProP 2 N → N ≤ W

/-- The packaging map: every AX4 bundle *is* a `LocalTameQuotientK`, maximality supplied by
`tameDataK_maximal`. -/
def OrientedTameQuotientK.toLocalTameQuotientK (T : OrientedTameQuotientK B FF) :
    LocalTameQuotientK B FF :=
  { toOrientedTameQuotientK := T, maximal := T.tameDataK_maximal }

/-! ### Tame reciprocity and the boundary compatibility (memo §1.9)

Both are **theorems over the two bundles**, not clauses.  The `ℚ₂` template is
`GQ2.SectionThree.tame_reciprocity` / `compatF_proved`; the one ingredient that changes is the
generator lemma: `padic_hom_eq_of_gens` (`ℚ₂ˣ = ⟨2⟩ × ⟨−3⟩`) is replaced by
`exists_unit_zpow_decomp` (`Kˣ = π^ℤ · O_K^×`), which is where `Aux.exists_norm_eq_zpow` enters. -/

namespace OrientedTameQuotientK

/-- `ι ∘ ν_t ∘ tameF_K : G_K →* Multiplicative ℤ₂`, before the descent through `G_K^{ab}`.  The
seam `ι` is `ztwoIota` = `GQ2.ztwoEquivPadic`, the `ι` of `prop_3_10_local_marked`. -/
def tameCharKRaw (T : OrientedTameQuotientK B FF) : GalK K →* Multiplicative ℤ_[2] :=
  (ztwoIota.toMulEquiv.toMonoidHom).comp
    ((nuTq (qOf K FF)).toMonoidHom.comp T.tameFK.toMonoidHom)

@[simp] theorem tameCharKRaw_apply (T : OrientedTameQuotientK B FF) (g : GalK K) :
    T.tameCharKRaw g = ztwoIota (nuTq (qOf K FF) (T.tameFK g)) := rfl

theorem continuous_tameCharKRaw (T : OrientedTameQuotientK B FF) : Continuous T.tameCharKRaw :=
  ztwoIota.continuous_toFun.comp
    ((nuTq (qOf K FF)).continuous_toFun.comp T.tameFK.continuous_toFun)

theorem commClosureK_le_ker_tameCharKRaw (T : OrientedTameQuotientK B FF) :
    commClosureK K ≤ T.tameCharKRaw.ker := by
  refine Subgroup.topologicalClosure_minimal _
    (Abelianization.commutator_subset_ker T.tameCharKRaw) ?_
  rw [MonoidHom.coe_ker]
  exact isClosed_singleton.preimage T.continuous_tameCharKRaw

/-- **The tame unramified character on `G_K^{ab}`** — `ι ∘ ν_t ∘ tameF_K` descended (well-posed:
the target is abelian and Hausdorff, so the closed commutator subgroup dies). -/
def tameCharK (T : OrientedTameQuotientK B FF) : GalKab K →* Multiplicative ℤ_[2] :=
  QuotientGroup.lift (commClosureK K) T.tameCharKRaw
    (fun _ hx => MonoidHom.mem_ker.mp (T.commClosureK_le_ker_tameCharKRaw hx))

@[simp] theorem tameCharK_toAbK (T : OrientedTameQuotientK B FF) (g : GalK K) :
    T.tameCharK (toAbK K g) = ztwoIota (nuTq (qOf K FF) (T.tameFK g)) := rfl

theorem continuous_tameCharK (T : OrientedTameQuotientK B FF) : Continuous T.tameCharK :=
  continuous_quot_lift _ T.continuous_tameCharKRaw

/-- **Atom (U)** — units: `f₁(rec_K u) = 1` for `‖u‖ = 1`, from the bundle's unit clause read at
any lift. -/
theorem tameCharK_recip_unit (T : OrientedTameQuotientK B FF) (u : (↥K)ˣ)
    (hu : ‖((u : ↥K) : ℚ̄₂)‖ = 1) : T.tameCharK (B.recip u) = 1 := by
  obtain ⟨g, hg⟩ := surjective_toAbK K (B.recip u)
  have hval : nuTq (qOf K FF) (T.tameFK g) = 1 := T.nuT_recip_unit u g hu hg
  rw [← hg, tameCharK_toAbK, hval, map_one]

/-- **Atom (F)** — B13's uniformizer: `f₁(rec_K π) = ofAdd(−1)` (arithmetic Frobenius, geometric
coordinate `−1`), from the bundle's uniformizer clause. -/
theorem tameCharK_recip_uniformizer (T : OrientedTameQuotientK B FF) :
    T.tameCharK (B.recip (uniformizerK K FF)) = Multiplicative.ofAdd ((-1 : ℤ) : ℤ_[2]) := by
  obtain ⟨g, hg⟩ := surjective_toAbK K (B.recip (uniformizerK K FF))
  have hval : nuTq (qOf K FF) (T.tameFK g) = ztwoOne⁻¹ := T.nuT_recip_uniformizer g hg
  rw [← hg, tameCharK_toAbK, hval, map_inv, ztwoIota_ztwoOne, ← ofAdd_neg]
  norm_num

/-- `f₁(rec_K x) = ofAdd(−n)` for `x = u·π^n` — the two atoms plus multiplicativity. -/
theorem tameCharK_recip (T : OrientedTameQuotientK B FF) (x : (↥K)ˣ) :
    T.tameCharK (B.recip x) = B.nu_ur (B.recip x) := by
  obtain ⟨u, n, hx, hu⟩ := exists_unit_zpow_decomp K FF x
  have hleft : T.tameCharK (B.recip x) = Multiplicative.ofAdd ((-n : ℤ) : ℤ_[2]) := by
    rw [hx, map_mul, map_mul, map_zpow, map_zpow, T.tameCharK_recip_unit u hu,
      T.tameCharK_recip_uniformizer, one_mul]
    refine Multiplicative.toAdd.injective ?_
    show (n • ((-1 : ℤ) : ℤ_[2])) = ((-n : ℤ) : ℤ_[2])
    rw [zsmul_eq_mul]
    push_cast
    ring
  rw [hleft, B.nu_ur_recip_of_decomp x u (uniformizerK K FF) n hx hu
    (norm_uniformizerK_lt_one K FF) (uniformizerK_max K FF)]

/-- **Tame reciprocity at `K`** (memo §1.9): `ι(ν_t(tameF_K g)) = ν_ur^K(g^{ab})`.  Both sides are
continuous homs out of `G_K^{ab}`; they agree on the dense image of `rec_K` (AX3's
`denseRange_recip`) because they agree on units and on B13's uniformizer — the two orientation
clauses of AX4 matched against AX3's `nu_ur_recip_unit` / `nu_ur_recip_uniformizer`.  **This clause
is derived, not asserted**: it is what the B1 boundary lane consumes. -/
theorem tame_reciprocity_K (T : OrientedTameQuotientK B FF) (g : GalK K) :
    ztwoIota (nuTq (qOf K FF) (T.tameFK g)) = B.nu_ur (toAbK K g) := by
  have key : ⇑T.tameCharK = ⇑B.nu_ur :=
    Continuous.ext_on B.denseRange_recip T.continuous_tameCharK B.continuous_nu_ur
      (by rintro _ ⟨x, rfl⟩; exact T.tameCharK_recip x)
  have h := congrFun key (toAbK K g)
  rwa [tameCharK_toAbK] at h

/-- **The boundary compatibility `ν_t ∘ tameF_K = ν₂ ∘ pro2F_K`** (memo §1.9, §0.1's F3 clause
(ii)), in the shape the B1 boundary lane instantiates it: for *any* pro-`2`-side coordinate
`(pro2F, ν₂)` whose composite is AX3's `ν_ur^K` through the seam `ι`, the tame and pro-`2`
unramified coordinates agree on the nose.  At `ℚ₂` the hypothesis `hpro` is
`prop_3_10_local_marked`'s `ν`-clause and the conclusion is `compatF_proved`. -/
theorem compatF_K {Pi : Type*} [Group Pi] [TopologicalSpace Pi] (T : OrientedTameQuotientK B FF)
    (pro2F : ContinuousMonoidHom (GalK K) Pi) (nuTwoK : ContinuousMonoidHom Pi Ztwo)
    (hpro : ∀ g : GalK K, ztwoIota (nuTwoK (pro2F g)) = B.nu_ur (toAbK K g))
    (g : GalK K) : nuTq (qOf K FF) (T.tameFK g) = nuTwoK (pro2F g) :=
  ztwoIota.injective (by rw [T.tame_reciprocity_K g, hpro g])

end OrientedTameQuotientK

/-! ### The orientation clause in the `DetRamified` packaging

`GQ2/DetRamified.lean`'s `prop_6_18_ramified` binds `horient : TameUnitOrientation R B.tameF`
(`GQ2/TameTwoQuotient.lean`), discharged at `ℚ₂` by `tameQuotient.nuT_recip_unit`
(`GQ2/TameOrientationWitness.lean`).  This is the general-`K` form of that `Prop`, and the AX4
bundle discharges it verbatim — the memo §0.1 entry that says DetRamified is the one LG-lane
consumer touching AX4's *orientation*, not just its existence. -/

/-- **`TameUnitOrientationK`** — the AX4 unit-orientation clause for an arbitrary tame coordinate
at `K`, the `GQ2.TameUnitOrientation` shape (`GQ2/TameTwoQuotient.lean`) at general `K`/`q`. -/
def TameUnitOrientationK {K : IntermediateField ℚ_[2] ℚ̄₂} [FiniteDimensional ℚ_[2] K]
    {R : LocalReciprocity} (B : MarkedRecip R K) (FF : DyadicUnitFiltration K)
    (tameF : ContinuousMonoidHom (GalK K) (Tq (qOf K FF))) : Prop :=
  ∀ (u : (↥K)ˣ) (g : GalK K), ‖((u : ↥K) : ℚ̄₂)‖ = 1 → toAbK K g = B.recip u →
    nuTq (qOf K FF) (tameF g) = 1

/-- The bundle discharges its own orientation clause at `tameF_K` — verbatim `nuT_recip_unit`, the
`GQ2.tameUnitOrientation_tameFHom` pattern. -/
theorem tameUnitOrientationK_tameFK (T : OrientedTameQuotientK B FF) :
    TameUnitOrientationK B FF T.tameFK :=
  T.nuT_recip_unit

end Derived

end

end GQ2.Dyadic
