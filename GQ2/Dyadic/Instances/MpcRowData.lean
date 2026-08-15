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

/-! ## §2 The determinant binder, wired

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
