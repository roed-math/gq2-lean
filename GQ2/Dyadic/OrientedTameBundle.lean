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

/-- `q_K` unfolded.  Deliberately **not** `@[simp]`: `qOf K FF` occurs as a type index in
`Tq (qOf K FF)`, and unfolding it inside a consumer's goal would force a transport where none is
needed. -/
theorem qOf_eq (FF : DyadicUnitFiltration K) : qOf K FF = 2 ^ FF.f := rfl

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

/-- `tameF_K` computed on an element (`rfl`).  Not `@[simp]`: consumers name `tameFK`, and the
bundle's `equiv`/`mk` spelling is an implementation detail. -/
theorem tameFK_apply (T : OrientedTameQuotientK B FF) (g : GalK K) :
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

/-! ## §4 `f` is an invariant of `K`, not of the filtration  (memo §1.4, and the R3 guard)

The obligation memo §1.4 attaches to the `DyadicUnitFiltration` parametrization: the residue degree
in the axiom's target does not depend on *which* filtration a consumer hands in.  Two uniformizers
have equal norm by `hπ_max` in both directions, so the whole depth filtration — and hence every
graded count — coincides; `e` then falls out of the `he` normalization and `f` out of
`card_gr_zero`.

**R3 (memo §7).**  This is the *only* pin available.  No `ν`-based test can see the odd part of
`f`: AX3's marked coordinate is `ℤ₂`-valued by design (plan §7.6), so a relation of the form
`ν_{ℚ₂} ∘ incl = f · ν_K` constrains only `v₂(f)` — for `f = 3` and `f = 1` the `ℤ₂`-images
coincide.  Any such test is therefore a *regression*, never a pin, and must not be presented as
one; the unit-filtration counts below are the witness.

**R2 (memo §7).**  The `q`-distinguishing guard lives in F3's file, kernel-`decide` proved and in
both of its forms: `card_hom_tq_zmodThree_two` / `card_hom_tq_zmodThree_four` (continuous-hom
counts `3` and `9`) and `card_tqTau_slot_zmodThree_two` / `card_tqTau_slot_zmodThree_four`
(inertia-slot counts `1` and `3`), assembled as `hom_count_distinguishes_tq_two_four`
(`GQ2/Dyadic/TameBoundary.lean`; the memo §4 correction block records that the memo's original
numbers were the inertia-slot ones).  They witness that the `q` in `Tq (qOf K FF)` is doing work,
hence that an unpinned `f` would be inconsistent.  They are not restated here: `TameBoundary.lean`
sits above the axiom layer and cannot be imported by this file. -/

section Uniqueness

variable {K : IntermediateField ℚ_[2] ℚ̄₂}

/-- Two B13 uniformizers of the same field have the same norm — `hπ_max` in both directions. -/
theorem norm_uniformizer_eq (FF FF' : DyadicUnitFiltration K) : ‖FF.π‖ = ‖FF'.π‖ :=
  le_antisymm (FF'.hπ_max _ FF.hπ_mem FF.hπ_lt) (FF.hπ_max _ FF'.hπ_mem FF'.hπ_lt)

/-- Hence the depth filtration itself does not depend on the chosen uniformizer. -/
theorem depthUnits_congr (FF FF' : DyadicUnitFiltration K) (i : ℕ) :
    depthUnits K FF.π i = depthUnits K FF'.π i := by
  ext u
  rw [mem_depthUnits, mem_depthUnits, norm_uniformizer_eq FF FF']

private theorem nat_eq_of_pow_eq_of_lt_one {t : ℝ} (h0 : 0 < t) (h1 : t < 1) {m n : ℕ}
    (h : t ^ m = t ^ n) : m = n :=
  (pow_right_strictAnti₀ h0 h1).injective h

/-- The absolute ramification index is an invariant of `K`. -/
theorem e_eq_of_filtration (FF FF' : DyadicUnitFiltration K) : FF.e = FF'.e := by
  have h : ‖FF.π‖ ^ FF.e = ‖FF.π‖ ^ FF'.e := by
    rw [← FF.he, FF'.he, norm_uniformizer_eq FF FF']
  exact nat_eq_of_pow_eq_of_lt_one (norm_pos_iff.mpr FF.hπ_ne) FF.hπ_lt h

/-- **The residue degree is an invariant of `K`** — the memo §1.4 obligation.  Both filtrations read
`2^f − 1` off the *same* graded piece `U⁰/U¹`, by `depthUnits_congr`. -/
theorem f_eq_of_filtration (FF FF' : DyadicUnitFiltration K) : FF.f = FF'.f := by
  have hcard : (2 : ℕ) ^ FF.f - 1 = 2 ^ FF'.f - 1 := by
    rw [← FF.card_gr_zero, ← FF'.card_gr_zero, depthUnits_congr FF FF' 1]
  have h1 : (2 : ℕ) ≤ 2 ^ FF.f := by
    calc (2 : ℕ) = 2 ^ 1 := (pow_one 2).symm
      _ ≤ 2 ^ FF.f := Nat.pow_le_pow_right (by norm_num) FF.hf_pos
  have h2 : (2 : ℕ) ≤ 2 ^ FF'.f := by
    calc (2 : ℕ) = 2 ^ 1 := (pow_one 2).symm
      _ ≤ 2 ^ FF'.f := Nat.pow_le_pow_right (by norm_num) FF'.hf_pos
  have hpow : (2 : ℕ) ^ FF.f = 2 ^ FF'.f := by omega
  exact Nat.pow_right_injective (le_refl 2) hpow

/-- Hence the axiom's target group is an invariant of `K`. -/
theorem qOf_eq_of_filtration (FF FF' : DyadicUnitFiltration K) : qOf K FF = qOf K FF' := by
  rw [qOf_eq, qOf_eq, f_eq_of_filtration FF FF']

end Uniqueness

/-! ## §5 The `K = ⊥` regression  (memo §3)

The merge-gate-8-style check that the general-`K` interface reproduces B10 at `ℚ₂`.  Steps 1–3 of
memo §3, all bundle-level: `e = 1`, `f = 1` (hence `q_⊥ = 2` and `T_{q_⊥} = Ttame` on the nose,
F3's `tq_two_equiv` being the identity — memo §7 R7), and `W_⊥ = W` from the two maximality
theorems.

**Step 1 is the R2 guard**: it is the only place in the campaign where `f` is *computed* from B13's
clauses rather than assumed, and what it computes is the arithmetic residue degree of `ℚ₂`.  The
computation runs through `card_gr_zero`: at `⊥` every norm-one unit is `≡ 1` modulo the maximal
ideal (residue field `𝔽₂`), so `U⁰ = U¹` and `2^f − 1 = 1`.

**Step 2's ⊥-transport is the consumer's.**  `W₂` below is B10's `GQ2.tameQuotient.W` pulled back
along `botGalEquiv`; its three hypotheses are B10's own clauses and `hmax₂` is
`GQ2.SectionThree.tameData_maximal` — all available exactly where the axioms are in scope, and none
of them nameable here (this file sits below `GQ2/Foundations/Axioms.lean`).  Memo §3 step 4 (the
orientation transport) and memo §6 point 2 record that plumbing as a separate project; the
statement below is the part that is bundle-level. -/

section Bot

/-- **The residue fact at `ℚ₂`**: a `2`-adic number of norm one is `≡ 1` modulo `2`.  Its image in
`ℤ_[2]` is a unit, hence nonzero in the residue field `ZMod 2`, hence `1`; so `z − 1` lies in the
maximal ideal.  (This is the `𝔽₂`-specific input: the ultrametric structure alone cannot see it —
in `ℚ₃`, `‖−1‖ = ‖−1 − 1‖ = 1`.) -/
private theorem padic_norm_sub_one_le_norm_two {c : ℚ_[2]} (hc : ‖c‖ = 1) :
    ‖c - 1‖ ≤ ‖(2 : ℚ_[2])‖ := by
  rcases eq_or_ne c 1 with rfl | hne
  · rw [sub_self, norm_zero]
    exact norm_nonneg _
  set z : ℤ_[2] := ⟨c, le_of_eq hc⟩ with hz
  have hzn : ‖z‖ = 1 := hc
  have hz0 : PadicInt.toZMod z ≠ 0 := by
    intro h0
    have hmem : z ∈ RingHom.ker (PadicInt.toZMod (p := 2)) := h0
    rw [PadicInt.ker_toZMod, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at hmem
    exact hmem (PadicInt.isUnit_iff.mpr hzn)
  have hz1 : PadicInt.toZMod z = 1 := (show ∀ x : ZMod 2, x ≠ 0 → x = 1 by decide) _ hz0
  have hltz : ‖(z - 1 : ℤ_[2])‖ < 1 := by
    have hmem : z - 1 ∈ RingHom.ker (PadicInt.toZMod (p := 2)) := by
      rw [RingHom.mem_ker, map_sub, hz1, map_one, sub_self]
    rw [PadicInt.ker_toZMod, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
      PadicInt.isUnit_iff] at hmem
    exact lt_of_le_of_ne (PadicInt.norm_le_one _) hmem
  have hlt : ‖c - 1‖ < 1 := by
    have hcoe : ((z - 1 : ℤ_[2]) : ℚ_[2]) = c - 1 := by push_cast; rfl
    rw [← hcoe, ← PadicInt.norm_def]
    exact hltz
  exact norm_le_norm_two_of_lt_one (sub_ne_zero_of_ne hne) hlt

/-- The `⊥`-form of the residue fact, in the spectral-norm vocabulary the B13 filtration uses. -/
theorem bot_norm_sub_one_le_norm_two {z : ↥(⊥ : IntermediateField ℚ_[2] ℚ̄₂)}
    (hz : ‖(z : ℚ̄₂)‖ = 1) : ‖(z : ℚ̄₂) - 1‖ ≤ ‖(2 : ℚ̄₂)‖ := by
  have hz' : ‖(IntermediateField.botEquiv ℚ_[2] ℚ̄₂ z : ℚ_[2])‖ = 1 := by
    rw [← norm_coe_bot z]; exact hz
  have hsub : ((z - 1 : ↥(⊥ : IntermediateField ℚ_[2] ℚ̄₂)) : ℚ̄₂) = (z : ℚ̄₂) - 1 := by
    push_cast; ring
  have h := padic_norm_sub_one_le_norm_two hz'
  rw [← hsub, norm_coe_bot (z - 1), norm_two_alg]
  refine le_of_le_of_eq ?_ rfl
  rw [show IntermediateField.botEquiv ℚ_[2] ℚ̄₂ (z - 1)
      = IntermediateField.botEquiv ℚ_[2] ℚ̄₂ z - 1 by rw [map_sub, map_one]]
  exact h

/-- **`‖π‖ = ‖2‖` at `⊥`**: `2` is a uniformizer of `ℚ₂` (AX3's `twoBot_max`), so `hπ_max` pins the
two norms against each other. -/
theorem bot_norm_uniformizer (FF : DyadicUnitFiltration (⊥ : IntermediateField ℚ_[2] ℚ̄₂)) :
    ‖FF.π‖ = ‖(2 : ℚ̄₂)‖ := by
  have h2mem : (2 : ℚ̄₂) ∈ (⊥ : IntermediateField ℚ_[2] ℚ̄₂) := by
    rw [← twoBot_coe]; exact SetLike.coe_mem _
  have h2lt : ‖(2 : ℚ̄₂)‖ < 1 := by rw [norm_two_alg]; exact norm_two_padic_lt_one
  refine le_antisymm ?_ (FF.hπ_max _ h2mem h2lt)
  have hπ0 : (⟨FF.π, FF.hπ_mem⟩ : ↥(⊥ : IntermediateField ℚ_[2] ℚ̄₂)) ≠ 0 :=
    fun h => FF.hπ_ne (congrArg Subtype.val h)
  have h := twoBot_max ⟨FF.π, FF.hπ_mem⟩ hπ0 FF.hπ_lt
  rwa [twoBot_coe] at h

/-- **Memo §3 step 1, the `e` half**: `e = 1` at `⊥`.  `‖2‖ = ‖π‖^e` with `‖π‖ = ‖2‖` forces
`e = 1`, since `0 < ‖π‖ < 1`. -/
theorem bot_e_eq_one (FF : DyadicUnitFiltration (⊥ : IntermediateField ℚ_[2] ℚ̄₂)) : FF.e = 1 := by
  have h : ‖FF.π‖ ^ FF.e = ‖FF.π‖ ^ 1 := by rw [← FF.he, pow_one, bot_norm_uniformizer FF]
  exact nat_eq_of_pow_eq_of_lt_one (norm_pos_iff.mpr FF.hπ_ne) FF.hπ_lt h

/-- At `⊥` the depth filtration collapses at level one: the residue field is `𝔽₂`, so *every*
norm-one unit is a principal unit.  This is the computation memo §3 step 1 rests on. -/
theorem bot_depthUnits_one (FF : DyadicUnitFiltration (⊥ : IntermediateField ℚ_[2] ℚ̄₂)) :
    depthUnits (⊥ : IntermediateField ℚ_[2] ℚ̄₂) FF.π 1 = normUnits ⊥ := by
  ext u
  rw [mem_depthUnits, mem_normUnits]
  refine ⟨fun h => h.1, fun h => ⟨h, ?_⟩⟩
  rw [pow_one, bot_norm_uniformizer FF]
  exact bot_norm_sub_one_le_norm_two h

/-- **Memo §3 step 1, the `f` half — the R2 guard.**  `f = 1` at `⊥`, *computed* from B13's
`card_gr_zero`: the graded piece `U⁰/U¹` is trivial by `bot_depthUnits_one`, so `2^f − 1 = 1`. -/
theorem bot_f_eq_one (FF : DyadicUnitFiltration (⊥ : IntermediateField ℚ_[2] ℚ̄₂)) : FF.f = 1 := by
  have hcard : Nat.card (↥(normUnits (⊥ : IntermediateField ℚ_[2] ℚ̄₂)) ⧸
      (depthUnits (⊥ : IntermediateField ℚ_[2] ℚ̄₂) FF.π 1).subgroupOf (normUnits ⊥)) = 1 := by
    rw [bot_depthUnits_one FF, Subgroup.subgroupOf_self]
    exact Subgroup.index_top
  have h := FF.card_gr_zero
  rw [hcard] at h
  have h1 : (2 : ℕ) ≤ 2 ^ FF.f := by
    calc (2 : ℕ) = 2 ^ 1 := (pow_one 2).symm
      _ ≤ 2 ^ FF.f := Nat.pow_le_pow_right (by norm_num) FF.hf_pos
  have hpow : (2 : ℕ) ^ FF.f = 2 ^ 1 := by rw [pow_one]; omega
  exact Nat.pow_right_injective (le_refl 2) hpow

/-- **Memo §3 step 3**: `q_⊥ = 2`. -/
theorem bot_qOf_eq_two (FF : DyadicUnitFiltration (⊥ : IntermediateField ℚ_[2] ℚ̄₂)) :
    qOf ⊥ FF = 2 := by rw [qOf_eq, bot_f_eq_one FF, pow_one]

/-- **Memo §3 step 3, the target identification**: `T_{q_⊥}` *is* the frozen `ℚ₂` tame group
`Ttame`, on the nose.  No transport is involved: `Tq 2` and `Ttame` are the same definition (F3's
`Tq_two` is `rfl`, and `tq_two_equiv` is `ContinuousMulEquiv.refl`), which is exactly what memo §7
R7 asks for — no second copy of `T_2` enters the library, so no `ℚ₂` capstone's axiom print can
change. -/
theorem bot_tq_eq_ttame (FF : DyadicUnitFiltration (⊥ : IntermediateField ℚ_[2] ℚ̄₂)) :
    Tq (qOf ⊥ FF) = Ttame := by rw [bot_qOf_eq_two FF]; exact Tq_two

/-- `G_⊥ = G_{ℚ₂}`: the transport handle for the `⊥` regression, `⊥.fixingSubgroup = ⊤`. -/
def botGalEquiv : GalK (⊥ : IntermediateField ℚ_[2] ℚ̄₂) ≃* AbsGalQ2 :=
  (MulEquiv.subgroupCongr (IntermediateField.fixingSubgroup_bot (F := ℚ_[2]) (E := ℚ̄₂))).trans
    Subgroup.topEquiv

@[simp] theorem botGalEquiv_apply (g : GalK (⊥ : IntermediateField ℚ_[2] ℚ̄₂)) :
    botGalEquiv g = (g : AbsGalQ2) := rfl

theorem continuous_botGalEquiv : Continuous botGalEquiv := continuous_subtype_val

variable {R : LocalReciprocity} {B : MarkedRecip R (⊥ : IntermediateField ℚ_[2] ℚ̄₂)}
  {FF : DyadicUnitFiltration (⊥ : IntermediateField ℚ_[2] ℚ̄₂)}

/-- **Memo §3 step 2: `W_⊥ = W`.**  Both wild subgroups are maximal closed normal pro-`2`, so they
coincide — the compatibility of memo §1.10, delivered as a theorem where it can be.  `W₂` is B10's
`W` pulled back along `botGalEquiv`; its clauses and `hmax₂` are B10's own data plus
`GQ2.SectionThree.tameData_maximal`, discharged by the consumer (this file cannot name the
axioms). -/
theorem bot_W_eq (T : OrientedTameQuotientK B FF)
    (W₂ : Subgroup (GalK (⊥ : IntermediateField ℚ_[2] ℚ̄₂))) (hnormal₂ : W₂.Normal)
    (hclosed₂ : IsClosed (W₂ : Set (GalK (⊥ : IntermediateField ℚ_[2] ℚ̄₂))))
    (hproP₂ : IsProP 2 W₂)
    (hmax₂ : ∀ N : Subgroup (GalK (⊥ : IntermediateField ℚ_[2] ℚ̄₂)), N.Normal →
      IsClosed (N : Set (GalK (⊥ : IntermediateField ℚ_[2] ℚ̄₂))) → IsProP 2 N → N ≤ W₂) :
    T.W = W₂ :=
  le_antisymm (hmax₂ T.W T.normal T.isClosed T.isProP)
    (T.tameDataK_maximal W₂ hnormal₂ hclosed₂ hproP₂)

/-- **The memo §3 regression, assembled.**  At `K = ⊥` an AX4 bundle reproduces B10: the
filtration invariants are the arithmetic ones (`e = f = 1`), the target is `q_⊥ = 2` and hence
literally `Ttame`, and the wild subgroup is B10's.  Read at `R := GQ2.localReciprocity`,
`B := markedRecipAt ⊥`, `T := orientedTameQuotientAt ⊥ FF` and `W₂ := GQ2.tameQuotient.W` pulled
back along `botGalEquiv`, this is the merge-gate-8 check that AX4 *extends* B10 rather than forking
it (memo §6: extend, do not replace). -/
theorem tameQuotientK_bot_reduces (T : OrientedTameQuotientK B FF)
    (W₂ : Subgroup (GalK (⊥ : IntermediateField ℚ_[2] ℚ̄₂))) (hnormal₂ : W₂.Normal)
    (hclosed₂ : IsClosed (W₂ : Set (GalK (⊥ : IntermediateField ℚ_[2] ℚ̄₂))))
    (hproP₂ : IsProP 2 W₂)
    (hmax₂ : ∀ N : Subgroup (GalK (⊥ : IntermediateField ℚ_[2] ℚ̄₂)), N.Normal →
      IsClosed (N : Set (GalK (⊥ : IntermediateField ℚ_[2] ℚ̄₂))) → IsProP 2 N → N ≤ W₂) :
    FF.e = 1 ∧ FF.f = 1 ∧ qOf ⊥ FF = 2 ∧ Tq (qOf ⊥ FF) = Ttame ∧ T.W = W₂ :=
  ⟨bot_e_eq_one FF, bot_f_eq_one FF, bot_qOf_eq_two FF, bot_tq_eq_ttame FF,
    bot_W_eq T W₂ hnormal₂ hclosed₂ hproP₂ hmax₂⟩

end Bot

/-! ## §6 Interim binder spellings and consumer-compatibility checks  (memo §5)

The **structure** — not the axiom — is what consumers name, so every spelling below keeps compiling
unchanged across the census flip; the flip merely supplies the canonical instance
(`orientedTameQuotientAt K FF`, and `dyadicUnitFiltration K` for `FF`).  Memo §5's binder block is

    variable {K : IntermediateField ℚ_[2] ℚ̄₂} [FiniteDimensional ℚ_[2] K]
    variable (B : MarkedRecip localReciprocity K)   -- AX3 (post-flip: `markedRecipAt K`)
    variable (FF : DyadicUnitFiltration K)          -- B13 (post-flip: `dyadicUnitFiltration K`)
    variable (T : OrientedTameQuotientK B FF)      -- AX4 (post-flip: `orientedTameQuotientAt K FF`)

and the reviewer's rule of thumb is: *if a statement mentions `T_q` only, it is F3 (axiom-free); if
it mentions `G_K` and `T_q` together, it is AX4.*

The `example`s at the end elaborate the instantiations the lanes' own docstrings prescribe, so that
a change to this file which broke them fails here rather than in a lane.  The consumer files
(`GQ2/Dyadic/LocalGauss/*.lean`, `GQ2/Dyadic/TameBoundary.lean`) sit far above the axiom layer and
cannot be imported here, so their binder shapes are written out. -/

section Binders

variable {K : IntermediateField ℚ_[2] ℚ̄₂} [FiniteDimensional ℚ_[2] K] {R : LocalReciprocity}
  {B : MarkedRecip R K} {FF : DyadicUnitFiltration K}

/-- **The tame target at `K`**, `T_{q_K}` — the spelling LG3/LG4/LG5 use as `Tq P.qK` and the
boundary lane uses as the first factor of `∂_K`. -/
abbrev TqK (K : IntermediateField ℚ_[2] ℚ̄₂) (FF : DyadicUnitFiltration K) : ProfiniteGrp :=
  Tq (qOf K FF)

omit [FiniteDimensional ℚ_[2] K] in
/-- **The bridge to F1's `FieldParameters`** (`GQ2/Dyadic/Parameters.lean`): the LG lane's `P.qK`
*is* `qOf K FF` as soon as the residue degrees agree.  This is the one line every LG call site
needs, and by §4's `f_eq_of_filtration` the right-hand side does not depend on the filtration. -/
theorem qOf_eq_qK (P : FieldParameters) (FF : DyadicUnitFiltration K) (hf : P.f = FF.f) :
    P.qK = qOf K FF := by rw [P.qK_eq, qOf_eq, hf]

omit [FiniteDimensional ℚ_[2] K] in
/-- The transport handle for a consumer that has already fixed an `F1` parameter record: the two
spellings of the tame target agree as objects, so a `Tq P.qK`-typed hom is an `Eq.mpr` away from a
`TqK K FF`-typed one. -/
theorem tq_qK_eq_TqK (P : FieldParameters) (FF : DyadicUnitFiltration K) (hf : P.f = FF.f) :
    Tq P.qK = TqK K FF :=
  congrArg Tq (qOf_eq_qK P FF hf)

/-- **The marking `ρ = c ∘ tameF_K`** that `prop_6_18_unramified_K` / `prop_6_18_ramified_K` bind as
the pair `(ρ, hfac)` (`GQ2/Dyadic/LocalGauss/Main.lean`). -/
def markingK {C : Type} [Group C] [TopologicalSpace C] (T : OrientedTameQuotientK B FF)
    (c : ContinuousMonoidHom (Tq (qOf K FF)) C) : ContinuousMonoidHom (GalK K) C :=
  c.comp T.tameFK

@[simp] theorem markingK_fac {C : Type} [Group C] [TopologicalSpace C]
    (T : OrientedTameQuotientK B FF) (c : ContinuousMonoidHom (Tq (qOf K FF)) C) (g : GalK K) :
    markingK T c g = c (T.tameFK g) := rfl

/-- `ρ` is surjective when `c` is — the `hρsurj` the LG lane derives from `htameFK`. -/
theorem markingK_surjective {C : Type} [Group C] [TopologicalSpace C]
    (T : OrientedTameQuotientK B FF) {c : ContinuousMonoidHom (Tq (qOf K FF)) C}
    (hc : Function.Surjective ⇑c) : Function.Surjective ⇑(markingK T c) :=
  hc.comp T.tameFK_surjective

section Checks

variable (T : OrientedTameQuotientK B FF)

/-- **LG-lane consumer check** (`GQ2/Dyadic/LocalGauss/Main.lean`'s `card_H1_eq_of_markingK`,
`prop_6_18_unramified_K`, `prop_6_18_ramified_K_of_package`).  Those theorems bind
`(tameFK : ContinuousMonoidHom ↥U (Tq P.qK)) (htameFK : Function.Surjective ⇑tameFK)` at
`U = K.fixingSubgroup = GalKsub K`, together with `(ρ, hfac, hρsurj)`; the AX4 bundle supplies all
five.  Written at the `TqK K FF` spelling — `Tq P.qK` is the same object by `tq_qK_eq_TqK`, which
is the consumer's one-line bridge. -/
example {C : Type} [Group C] [TopologicalSpace C] (c : ContinuousMonoidHom (TqK K FF) C)
    (hc : Function.Surjective ⇑c) :
    ∃ (tameF : ContinuousMonoidHom (GalK K) (TqK K FF)) (ρ : ContinuousMonoidHom (GalK K) C),
      Function.Surjective ⇑tameF ∧ (∀ g, ρ g = c (tameF g)) ∧ Function.Surjective ⇑ρ :=
  ⟨T.tameFK, markingK T c, T.tameFK_surjective, markingK_fac T c, markingK_surjective T hc⟩

/-- **DetRamified consumer check** (`GQ2/DetRamified.lean`'s `prop_6_18_ramified`, whose K-side
retype binds `horient : TameUnitOrientationK B FF tameFK`).  This is the one LG-lane hypothesis that
touches AX4's *orientation* rather than only its existence, and the bundle discharges it. -/
example : TameUnitOrientationK B FF T.tameFK := tameUnitOrientationK_tameFK T

/-- **Boundary-lane consumer check** (F3's Thm. 3.5 field side,
`GQ2/Dyadic/TameBoundary.lean`).  What lands `g` in the fibre product
`∂_K = T_{q_K} ×_{ℤ₂} D_K` is the equalizer condition on the pair `(tameF_K g, pro2F_K g)`; AX4
enters through `tameFK` and `compatF_K` only, and `compatF_K` is *derived*. -/
example {Pi : Type} [Group Pi] [TopologicalSpace Pi] (pro2F : ContinuousMonoidHom (GalK K) Pi)
    (nuTwoK : ContinuousMonoidHom Pi Ztwo)
    (hpro : ∀ g : GalK K, ztwoIota (nuTwoK (pro2F g)) = B.nu_ur (toAbK K g)) :
    ∀ g : GalK K, (T.tameFK g, pro2F g) ∈
      {p : Tq (qOf K FF) × Pi | nuTq (qOf K FF) p.1 = nuTwoK p.2} :=
  fun g => T.compatF_K pro2F nuTwoK hpro g

/-- **B1 boundary-package consumer check**: the `BoundaryMaps`-analogue fields the MC5 lane
assembles at `K` — `tameF_K` surjective with pro-`2` kernel `W_K` (`ker_tameFK` + the bundle's
`isProP`), `W_K` maximal (derived), and the tame-reciprocity identity.  All four are theorems over
the bundle; none is a clause. -/
example : Function.Surjective ⇑T.tameFK ∧ T.tameFK.toMonoidHom.ker = T.W ∧ IsProP 2 T.W ∧
    (∀ N : Subgroup (GalK K), N.Normal → IsClosed (N : Set (GalK K)) → IsProP 2 N → N ≤ T.W) ∧
    (∀ g : GalK K, ztwoIota (nuTq (qOf K FF) (T.tameFK g)) = B.nu_ur (toAbK K g)) :=
  ⟨T.tameFK_surjective, T.ker_tameFK, T.isProP, T.tameDataK_maximal, T.tame_reciprocity_K⟩

end Checks

end Binders

end

end GQ2.Dyadic
