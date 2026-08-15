/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Opus-5
-/
import GQ2.Dyadic.Instances.FieldBranchIdentification
import GQ2.Dyadic.MarkedCore.MFrameExists
import GQ2.Dyadic.MarkedCore.NFrameExists

/-!
# W78-UNIMOD: the last clause on the five quadratic branch data

## The ticket

`docs/dyadic/w77-field-note.md` §7 item 1.  Wave 77 closed the branch identification at all five
frozen quadratic rows and left, at each, exactly one clause: the marked-data pair unimodularity,
`hpivot` on an `M` row (`ν_ur` a unit at the image of `C̄₀`) and `hpair` on the `N` pilot (at the
image of `σ` or of `x₂`).  The ticket asks whether the tree's stronger level-zero producers
`marked_matching_certificate_KTwo{M,N}_of_level_zero` (`LabuteInterface.lean:81`, `:123`) remove
that clause, since they take `B.r = 0` plus a decomposition instead.

## What this file establishes

**The clause and the level are the same hypothesis.**  Not "the level route is an alternative
to the pivot route": at `α ≥ 2` and `h = 0` the two are *equivalent*, and the equivalence is
proved here in both directions:

* `fieldUni_level_zero_of_pivotM`, `fieldUni_level_zero_of_pairN` — the clause **forces**
  `B.r = 0`;
* `fieldUni_pivotM_of_level_zero`, `fieldUni_pairN_of_level_zero` — and conversely;
* `fieldUni_pivotM_iff_level_zero`, `fieldUni_pairN_iff_level_zero` — the two `iff`s.

The forward direction is the one with consequences.  `chiM_dmC` puts the pivot `C̄₀` in `ker χ_M`,
so an oriented equivalence carries it into `ker χ_cyc` on `G_K(2)`; `nu_ker_chi_le` then reads
`ν_ur` there inside `2^r ℤ₂`, and a unit value collapses `r`.  So a lane cannot dodge the level
by choosing a different equivalence, a different frame, or a different `α`: **on any `M0` or `N0`
row the residual clause is exactly `B.r = 0`.**

⚠ [W79-HOUSE, as of `527adf51`: that bolded sentence drops the two qualifiers this docstring
carried correctly twelve lines above.  Read it as **on any `M0 α 0` or `N0 α 0` row with
`α ≥ 2`**: the `iff`s are proved at `α ≥ 2` and `h = 0`, which is where all five frozen rows
sit, and not beyond.]

That in turn is what the tree's own selector says: `FieldBranchSelector.lean:464` and `:470`
match `.M0 β` and `.N0 β` only against `Q.r = 0`.  §1's equivalence is the semantic form of that
syntactic side condition.

## The five fields, and the two that are not level zero

`B.r` is a **field of the bundle**, not a derived quantity: `MarkedRecipBundle.lean:598`.  It is
pinned by the two level clauses (`nu_ker_chi_le`, `nu_ker_chi_ge`), which determine it uniquely
(`2^r ℤ₂ = 2^s ℤ₂ → r = s`), so "is `B.r = 0` at this field" is a genuine arithmetic question
about `K` and not a modelling choice.  The answer is **not** uniform across the five rows:

| row | field | level | this file |
| --- | --- | --- | --- |
| `sqrtNegTwo` | `ℚ₂(√−2)` | `r = 0` | `fieldUni_level_sqrtNegTwo`, proved |
| `sqrtTwo` | `ℚ₂(√2)` | `r = 0` | `fieldUni_level_sqrtTwo`, proved |
| `sqrtFive` | `ℚ₂(√5)` | `r = 0` | reduced to `fieldUni_TwoIsUniformizer`, §4 |
| `sqrtTen` | `ℚ₂(√10)` | `r = 1` | **false**, see §5 |
| `sqrtNegTen` | `ℚ₂(√−10)` | `r = 1` | **false**, see §5 |

The last two entries are the lane's correction to wave 77.  `ℚ₂(√10)` and `ℚ₂(√−10)` are
level **one**: `K(√5) ⊆ K(μ₈)` is an unramified quadratic extension at both (`√10·√2 = 2√5`, and
`√−10·√2 = 2√−5` with `i ∈ K(μ₄)`), so `ν_ur(ker χ) = 2ℤ₂`.  Equivalently on the norm side, `2^k`
is a norm from `ℚ₂(√10)` only for even `k` (`(2, 10)₂ = −1`), and no element of odd valuation
there has a norm whose unit part is `1`.  That refutation is a hand computation; it is **not**
formalized here, and §5 states nothing about those two fields beyond what §1 proves — that their
residual clause *is* the level equation.  It also matches the frozen table, which puts both rows
on `.Mpc 2 1 _ 1`, valid only with `1 ≤ r` (`Main.lean:136`, `:137`, `:228`).

## Numbering

1. the clause is the level: the two `iff`s;
2. the level-zero branch-datum producers, with no residual clause;
3. the level criterion from an element of `Kˣ`, and the two ramified fields that meet it;
4. `ℚ₂(√5)`, reduced to one named unramifiedness Prop;
5. the five rows;
6. axiom pins.
-/

namespace GQ2.Dyadic.FieldUnimod

open GQ2 GQ2.Dyadic.MarkedCore
open GQ2.Dyadic.Fields GQ2.Dyadic.FieldBranchId GQ2.Dyadic.EvenRangePolish

local notation "ℚ̄₂" => AlgebraicClosure ℚ_[2]

noncomputable section

/-! ## §1 The clause is the level

`chiM_dmC` and `chiN_dnSigma`/`chiN_dnX2` put the marked pivots inside `ker χ` on the abstract
core.  An oriented equivalence transports that to `ker χ_cyc` on `G_K(2)`, where
`nu_ker_chi_le` confines `ν_ur` to `2^r ℤ₂`.  So a unit value at a pivot forces `r = 0`, and the
converse is the tree's own change of variables (`isUnit_nu_dmC_of_chiKer`,
`nPairUnimodular_of_chiKer`) fed by `nu_ker_chi_ge 1`. -/

section Criterion

variable {K : IntermediateField ℚ_[2] ℚ̄₂} [FiniteDimensional ℚ_[2] K]
  [CompactSpace (GalK K)] [TotallyDisconnectedSpace (GalK K)]
  {Rec : LocalReciprocity}

omit [CompactSpace (GalK K)] [TotallyDisconnectedSpace (GalK K)] in
/-- **The level criterion on `G_K^{ab}`**: one `ker χ` class of unit `ν_ur`-value collapses the
marked level.  This is `bot_level_eq_zero`'s argument with the witness abstracted out. -/
theorem fieldUni_level_eq_zero_of_chiKer (B : MarkedRecip Rec K) {g : GalKab K}
    (hchi : chiCycKAb K g = 1) (hunit : IsUnit (Multiplicative.toAdd (B.nu_ur g))) :
    B.r = 0 := by
  by_contra hr
  obtain ⟨y, hy⟩ := B.nu_ker_chi_le g hchi
  have hz : PadicInt.toZMod (Multiplicative.toAdd (B.nu_ur g)) = 0 := by
    rw [hy, map_mul, map_pow, map_ofNat, show ((2 : ZMod 2)) = 0 from by decide,
      zero_pow hr, zero_mul]
  exact not_isUnit_zero (hz ▸ hunit.map (PadicInt.toZMod (p := 2)))

/-- **The level criterion on `G_K(2)`**, where the marked-core producers read their data.  Both
canonical characters descend through `maxProPMk`, so the criterion transports verbatim. -/
theorem fieldUni_level_eq_zero_of_chiKerTwo (B : MarkedRecip Rec K)
    {q : maxProPQuotient 2 (GalK K)} (hchi : chiCycKTwo (K := K) q = 1)
    (hunit : IsUnit (Multiplicative.toAdd (nuUrKTwo B q))) : B.r = 0 := by
  obtain ⟨g, rfl⟩ := maxProPMk_surjective (p := 2) (G := GalK K) q
  rw [chiCycKTwo_maxProPMk, ← chiCycKAb_toAbK] at hchi
  rw [nuUrKTwo_maxProPMk] at hunit
  exact fieldUni_level_eq_zero_of_chiKer B hchi hunit

variable (B : MarkedRecip Rec K)

/-- **The `M` pivot clause forces level zero.**  `C̄₀` lies in `ker χ_M`, so its image lies in
`ker χ_cyc`. -/
theorem fieldUni_level_zero_of_pivotM {alpha : ℕ}
    (e : OrientedContinuousMulEquiv (chiM alpha 0) (chiCycKTwo (K := K)))
    (hpivot : IsUnit (Multiplicative.toAdd (nuUrKTwo B (e.1 (dmC alpha 0))))) : B.r = 0 := by
  have h : chiCycKTwo (K := K) (e.1 (dmC alpha 0)) = chiM alpha 0 (dmC alpha 0) := e.2 _
  exact fieldUni_level_eq_zero_of_chiKerTwo B (h.trans (chiM_dmC alpha 0)) hpivot

/-- **The `N` pair clause forces level zero.**  Both `σ` and `x₂` lie in `ker χ_N`, so either
disjunct suffices. -/
theorem fieldUni_level_zero_of_pairN {alpha : ℕ}
    (e : OrientedContinuousMulEquiv (chiN alpha 0) (chiCycKTwo (K := K)))
    (hpair : IsUnit (Multiplicative.toAdd (nuUrKTwo B (e.1 (dnSigma alpha 0)))) ∨
      IsUnit (Multiplicative.toAdd (nuUrKTwo B (e.1 (dnX2 alpha 0))))) : B.r = 0 := by
  rcases hpair with hu | hu
  · have h : chiCycKTwo (K := K) (e.1 (dnSigma alpha 0)) = chiN alpha 0 (dnSigma alpha 0) := e.2 _
    exact fieldUni_level_eq_zero_of_chiKerTwo B (h.trans (chiN_dnSigma alpha 0)) hu
  · have h : chiCycKTwo (K := K) (e.1 (dnX2 alpha 0)) = chiN alpha 0 (dnX2 alpha 0) := e.2 _
    exact fieldUni_level_eq_zero_of_chiKerTwo B (h.trans (chiN_dnX2 alpha 0)) hu

/-- The `ν_ur`-marking of the abstract core pulled back along an oriented equivalence: the
object the compact change of variables is stated against. -/
def fieldUni_nuPullbackM {alpha : ℕ}
    (e : OrientedContinuousMulEquiv (chiM alpha 0) (chiCycKTwo (K := K))) :
    ContinuousMonoidHom (DM alpha 0 : Type) (Multiplicative ℤ_[2]) where
  toFun x := nuUrKTwo B (e.1 x)
  map_one' := by rw [map_one, map_one]
  map_mul' x y := by rw [map_mul, map_mul]
  continuous_toFun := (nuUrKTwo B).continuous_toFun.comp e.1.continuous_toFun

/-- The `N` analogue of `fieldUni_nuPullbackM`. -/
def fieldUni_nuPullbackN {alpha : ℕ}
    (e : OrientedContinuousMulEquiv (chiN alpha 0) (chiCycKTwo (K := K))) :
    ContinuousMonoidHom (DN alpha 0 : Type) (Multiplicative ℤ_[2]) where
  toFun x := nuUrKTwo B (e.1 x)
  map_one' := by rw [map_one, map_one]
  map_mul' x y := by rw [map_mul, map_mul]
  continuous_toFun := (nuUrKTwo B).continuous_toFun.comp e.1.continuous_toFun

/-- At level zero the pulled-back marking is unimodular somewhere on `ker χ`: the class supplied
by `nu_ker_chi_ge 1`, transported to the core through the equivalence.  This is the step the
level-zero certificate producers perform internally. -/
theorem fieldUni_chiKerUnimodularM {alpha : ℕ} (hr : B.r = 0)
    (e : OrientedContinuousMulEquiv (chiM alpha 0) (chiCycKTwo (K := K))) :
    MChiKerUnimodular alpha 0 (fieldUni_nuPullbackM B e) := by
  obtain ⟨gbar, hgchi, hgnu⟩ := B.nu_ker_chi_ge 1
  obtain ⟨g, rfl⟩ := surjective_toAbK K gbar
  refine ⟨e.1.symm (maxProPMk 2 (GalK K) g), ?_, ?_⟩
  · have h : chiCycKTwo (K := K) (e.1 (e.1.symm (maxProPMk 2 (GalK K) g)))
        = chiM alpha 0 (e.1.symm (maxProPMk 2 (GalK K) g)) := e.2 _
    rw [e.1.apply_symm_apply, chiCycKTwo_maxProPMk, ← chiCycKAb_toAbK] at h
    exact h.symm.trans hgchi
  · show IsUnit (Multiplicative.toAdd (nuUrKTwo B (e.1 (e.1.symm (maxProPMk 2 (GalK K) g)))))
    rw [e.1.apply_symm_apply, nuUrKTwo_maxProPMk, hgnu, hr, pow_zero, one_mul]
    exact isUnit_one

/-- The `N` analogue of `fieldUni_chiKerUnimodularM`. -/
theorem fieldUni_chiKerUnimodularN {alpha : ℕ} (hr : B.r = 0)
    (e : OrientedContinuousMulEquiv (chiN alpha 0) (chiCycKTwo (K := K))) :
    NChiKerUnimodular alpha 0 (fieldUni_nuPullbackN B e) := by
  obtain ⟨gbar, hgchi, hgnu⟩ := B.nu_ker_chi_ge 1
  obtain ⟨g, rfl⟩ := surjective_toAbK K gbar
  refine ⟨e.1.symm (maxProPMk 2 (GalK K) g), ?_, ?_⟩
  · have h : chiCycKTwo (K := K) (e.1 (e.1.symm (maxProPMk 2 (GalK K) g)))
        = chiN alpha 0 (e.1.symm (maxProPMk 2 (GalK K) g)) := e.2 _
    rw [e.1.apply_symm_apply, chiCycKTwo_maxProPMk, ← chiCycKAb_toAbK] at h
    exact h.symm.trans hgchi
  · show IsUnit (Multiplicative.toAdd (nuUrKTwo B (e.1 (e.1.symm (maxProPMk 2 (GalK K) g)))))
    rw [e.1.apply_symm_apply, nuUrKTwo_maxProPMk, hgnu, hr, pow_zero, one_mul]
    exact isUnit_one

/-- **Level zero gives the `M` pivot clause**, through the compact change of variables. -/
theorem fieldUni_pivotM_of_level_zero {alpha : ℕ} (halpha : 2 ≤ alpha) (hr : B.r = 0)
    (e : OrientedContinuousMulEquiv (chiM alpha 0) (chiCycKTwo (K := K))) :
    IsUnit (Multiplicative.toAdd (nuUrKTwo B (e.1 (dmC alpha 0)))) := by
  obtain ⟨D⟩ := mFrameExists_mDecomposition (α := alpha) (by omega)
  exact isUnit_nu_dmC_of_chiKer halpha D _ (fieldUni_chiKerUnimodularM B hr e)

/-- **Level zero gives the `N` pair clause**, through the compact change of variables. -/
theorem fieldUni_pairN_of_level_zero {alpha : ℕ} (halpha : 2 ≤ alpha) (hr : B.r = 0)
    (e : OrientedContinuousMulEquiv (chiN alpha 0) (chiCycKTwo (K := K))) :
    IsUnit (Multiplicative.toAdd (nuUrKTwo B (e.1 (dnSigma alpha 0)))) ∨
      IsUnit (Multiplicative.toAdd (nuUrKTwo B (e.1 (dnX2 alpha 0)))) := by
  obtain ⟨D⟩ := nFrameExists_nDecomposition (α := alpha) halpha
  exact nPairUnimodular_of_chiKer halpha D _ (fieldUni_chiKerUnimodularN B hr e)

/-- **THE `M` ROW'S RESIDUAL CLAUSE IS THE LEVEL.**  At `α ≥ 2` and `h = 0` the pivot
unimodularity `hpivot` of `genAsm_branch_of_evenM` and the arithmetic level equation `B.r = 0`
are the same hypothesis, at every oriented equivalence. -/
theorem fieldUni_pivotM_iff_level_zero {alpha : ℕ} (halpha : 2 ≤ alpha)
    (e : OrientedContinuousMulEquiv (chiM alpha 0) (chiCycKTwo (K := K))) :
    IsUnit (Multiplicative.toAdd (nuUrKTwo B (e.1 (dmC alpha 0)))) ↔ B.r = 0 :=
  ⟨fieldUni_level_zero_of_pivotM B e, fun hr => fieldUni_pivotM_of_level_zero B halpha hr e⟩

/-- **THE `N` ROW'S RESIDUAL CLAUSE IS THE LEVEL.**  The `hpair` analogue of
`fieldUni_pivotM_iff_level_zero`. -/
theorem fieldUni_pairN_iff_level_zero {alpha : ℕ} (halpha : 2 ≤ alpha)
    (e : OrientedContinuousMulEquiv (chiN alpha 0) (chiCycKTwo (K := K))) :
    (IsUnit (Multiplicative.toAdd (nuUrKTwo B (e.1 (dnSigma alpha 0)))) ∨
        IsUnit (Multiplicative.toAdd (nuUrKTwo B (e.1 (dnX2 alpha 0))))) ↔ B.r = 0 :=
  ⟨fieldUni_level_zero_of_pairN B e, fun hr => fieldUni_pairN_of_level_zero B halpha hr e⟩

end Criterion

/-! ## §2 The level-zero branch-datum producers

The analogues of `GeneralAssembly.genAsm_branch_of_even{M,N}` routed through the compact
level-zero certificate producers.  Two differences from the committed pair: the decomposition
binder is discharged from the tree's existence theorems (`mFrameExists_mDecomposition`,
`nFrameExists_nDecomposition`), and `hMix` disappears on the `M` side, the level-zero producer
having no such binder.  What remains is `B.r = 0` and the oriented equivalence. -/

section Producer

variable {K : IntermediateField ℚ_[2] ℚ̄₂} [FiniteDimensional ℚ_[2] K]
  [CompactSpace AbsGalQ2] [TotallyDisconnectedSpace AbsGalQ2]
  [CompactSpace (GalK K)] [TotallyDisconnectedSpace (GalK K)]
  {Rec : LocalReciprocity} {B : MarkedRecip Rec K}

/-- **The `M0` branch datum at level zero.**  `marked_matching_certificate_KTwoM_of_level_zero`
in place of `marked_matching_certificate_KTwoM`: the `MDecomposition` binder is filled from
`mFrameExists_mDecomposition` and `hMix` is gone, so the only inputs are the degree pin, the
oriented equivalence and `B.r = 0`.

⚠ [W79-HOUSE, as of `527adf51`: four inputs, not three.  `halpha : 2 ≤ alpha` is also carried
and is not implied by `hdeg`.  The `N0` twin below enumerates nothing and is clean.]

**[W83-RECORDS: the conclusion now carries the marking**, `fieldId_mNuZtwo alpha 0`.  This is
one of the five sites of that lane; see `GeneralAssembly.genAsm_branch_of_oddSq` for why the
conjunct is `HEq` and how a consumer turns it back into an equation.  Without it no consumer of
this producer could reach `GenAsmRowResidual.cand`, whose committed producer on this row
(`Instances.MCompactCore.mWordCertificate`) is stated at a *named* marking.  The proof is
unchanged apart from the extra `HEq.rfl`.]** -/
theorem fieldUni_genAsmBranch_of_orientedM_level_zero (alpha : ℕ) (halpha : 2 ≤ alpha)
    (hdeg : Module.finrank ℚ_[2] K = (SelectedPresentation.M0 alpha 0).degree)
    (hr : B.r = 0)
    (e : OrientedContinuousMulEquiv (chiM alpha 0) (chiCycKTwo (K := K))) :
    ∃ G : GenAsmBranch K B, G.pres = .M0 alpha 0 ∧
      HEq G.nuP (fieldId_mNuZtwo alpha 0 (by omega)) := by
  obtain ⟨D⟩ := mFrameExists_mDecomposition (α := alpha) (by omega)
  obtain ⟨C⟩ := marked_matching_certificate_KTwoM_of_level_zero B alpha halpha D hr e.1 e.2
  exact ⟨{ pres := .M0 alpha 0, hdeg := hdeg,
           nuP := fieldId_mNuZtwo alpha 0 (by omega),
           hnuP := fieldId_mNuZtwo_surjective alpha 0 (by omega),
           realization := MarkedCoreRealization.ofCertificateM _
             (fieldId_ztwoIota_mNuZtwo alpha 0 (by omega)) C }, rfl, HEq.rfl⟩

/-- **The `N0` branch datum at level zero**, through
`marked_matching_certificate_KTwoN_of_level_zero` and `nFrameExists_nDecomposition`.

**[W83-RECORDS: the conclusion now carries the marking**, `nNuZtwo alpha 0`, for the reason
recorded on the `M0` twin above.]** -/
theorem fieldUni_genAsmBranch_of_orientedN_level_zero (alpha : ℕ) (halpha : 2 ≤ alpha)
    (hdeg : Module.finrank ℚ_[2] K = (SelectedPresentation.N0 alpha 0).degree)
    (hr : B.r = 0)
    (e : OrientedContinuousMulEquiv (chiN alpha 0) (chiCycKTwo (K := K))) :
    ∃ G : GenAsmBranch K B, G.pres = .N0 alpha 0 ∧
      HEq G.nuP (GQ2.Dyadic.SelectedCoreLeavesRN.nNuZtwo alpha 0) := by
  obtain ⟨D⟩ := nFrameExists_nDecomposition (α := alpha) halpha
  obtain ⟨C⟩ := marked_matching_certificate_KTwoN_of_level_zero B alpha halpha D hr e.1 e.2
  exact ⟨{ pres := .N0 alpha 0, hdeg := hdeg,
           nuP := GQ2.Dyadic.SelectedCoreLeavesRN.nNuZtwo alpha 0,
           hnuP := GQ2.Dyadic.genCertNNuZtwo_surjective alpha 0,
           realization := MarkedCoreRealization.ofCertificateN _
             (fieldId_ztwoIota_nNuZtwo alpha 0) C }, rfl, HEq.rfl⟩

end Producer

/-! ## §3 The level at a field, from one element of `Kˣ`

`B.r` is a bundle field, so it is not "computed"; it is *pinned* by the two level clauses.  The
usable half is `nu_ker_chi_le`: one `x : Kˣ` whose class lies in `ker χ` and whose `ν`-value is
odd forces `r = 0`.  Both halves are read off the same bundle clauses that `EvenRangePolish` and
`FieldBranchIdentification` use:

* `χ_K(rec_K x) = 1` exactly when `N_{K/ℚ₂}(x)` is a power of `2` **with unit part `1`**
  (`norm_compat` plus the base bundle's clauses (c) at units and at the uniformizer);
* `ν_ur(rec_K x) = ofAdd(−1)` when `x` is a uniformizer times a spectral unit
  (`nu_ur_recip_of_decomp`).

At a quadratic field with `v(a) = 1` the element `√a` *is* a uniformizer, which §3.2 proves from
`Fields.lean` §4's separation lemma; that is what makes §3.3's two rows unconditional. -/

section FieldLevel

variable {K : IntermediateField ℚ_[2] ℚ̄₂} [FiniteDimensional ℚ_[2] K]
  [CompactSpace (GalK K)] [TotallyDisconnectedSpace (GalK K)]
  {Rec : LocalReciprocity}

open GQ2.Dyadic.LSquare

omit [CompactSpace (GalK K)] [TotallyDisconnectedSpace (GalK K)] in
/-- **The cyclotomic value at an element of known norm.**  `fieldId_inv_mem_range_of_norm` as an
equation rather than a membership: `χ_K(rec_K x) = u⁻¹` when `N(x) = u · 2^n`. -/
theorem fieldUni_chi_recip_of_norm (B : MarkedRecip Rec K) (x : (↥K)ˣ) (u : ℤ_[2]ˣ) (n : ℕ)
    (hx : normUnitsK K x = unitEmbed u * uniformizer ^ n) :
    chiCycKAb K (B.recip x) = u⁻¹ := by
  rw [← chiCycAb_inclAbK, B.norm_compat, hx]
  simp only [map_mul, map_pow, Rec.chiCyc_recip_unit, Rec.chiCyc_recip_uniformizer, one_pow,
    mul_one]

omit [CompactSpace (GalK K)] [TotallyDisconnectedSpace (GalK K)] in
/-- **The level from one element.**  `x = u · π` with `u` a spectral unit and `π` a uniformizer
gives `ν_ur(rec_K x) = ofAdd(−1)`, a unit; with `χ_K(rec_K x) = 1` the level clause collapses. -/
theorem fieldUni_level_eq_zero_of_decomp (B : MarkedRecip Rec K) (x u pi : (↥K)ˣ)
    (hchi : chiCycKAb K (B.recip x) = 1) (hx : x = u * pi ^ (1 : ℤ))
    (hu : ‖((u : ↥K) : ℚ̄₂)‖ = 1) (hpi : ‖((pi : ↥K) : ℚ̄₂)‖ < 1)
    (hmax : ∀ z : ↥K, z ≠ 0 → ‖(z : ℚ̄₂)‖ < 1 → ‖(z : ℚ̄₂)‖ ≤ ‖((pi : ↥K) : ℚ̄₂)‖) :
    B.r = 0 := by
  refine fieldUni_level_eq_zero_of_chiKer B hchi ?_
  rw [B.nu_ur_recip_of_decomp x u pi 1 hx hu hpi hmax]
  have hval : Multiplicative.toAdd (Multiplicative.ofAdd (((-1 : ℤ) : ℤ_[2]))) = -1 := by
    push_cast
    rfl
  rw [hval]
  exact isUnit_one.neg

end FieldLevel

/-! ### §3.2 `√a` is a uniformizer when `v(a) = 1`

`Fields.lean` §4 proves the separation lemma `‖x‖ ≠ ‖y√a‖` for odd `v(a)` and, from it, the exact
norm `‖x + y√a‖ = max(‖x‖, ‖y√a‖)`.  With `‖a‖ = ‖2‖` that identifies the value group: the
scalar part is at most `‖2‖ ≤ ‖√a‖` once it is `< 1`, and the `√a` part is at most `‖√a‖` because
a scalar of norm `> 1` has norm at least `2`, which `√a` cannot absorb.  So `√a` attains the
maximal norm below `1`, which is exactly the B13 uniformizer spec of
`MarkedRecip.nu_ur_recip_uniformizer`. -/

section Uniformizer

variable {a : ℚ_[2]}

/-- `‖2‖ = 1/2` on the nose, so the estimates below are ordinary real arithmetic. -/
theorem fieldUni_norm_two : ‖(2 : ℚ_[2])‖ = (2 : ℝ)⁻¹ := by
  rw [show (2 : ℚ_[2]) = ((2 : ℕ) : ℚ_[2]) by push_cast; ring, Padic.norm_p]
  norm_num

/-- `‖√a‖ < 1` when `‖a‖ = ‖2‖`. -/
theorem fieldUni_norm_sqrtIn_lt_one (hna : ‖a‖ = ‖(2 : ℚ_[2])‖) : ‖sqrtIn a‖ < 1 := by
  have hsq := norm_sqrtIn_sq a
  rw [hna, fieldUni_norm_two] at hsq
  nlinarith [norm_nonneg (sqrtIn a)]

/-- `‖2‖ ≤ ‖√a‖` when `‖a‖ = ‖2‖`: the scalar uniformizer of `ℚ₂` is not maximal upstairs. -/
theorem fieldUni_norm_two_le_sqrtIn (hna : ‖a‖ = ‖(2 : ℚ_[2])‖) :
    ‖(2 : ℚ_[2])‖ ≤ ‖sqrtIn a‖ := by
  have hsq := norm_sqrtIn_sq a
  rw [hna, fieldUni_norm_two] at hsq
  rw [fieldUni_norm_two]
  nlinarith [norm_nonneg (sqrtIn a)]

/-- A scalar of norm `> 1` has norm at least `2`, so it cannot be shrunk below `1` by `√a`. -/
theorem fieldUni_norm_le_one_of_mul_sqrtIn_lt_one (hna : ‖a‖ = ‖(2 : ℚ_[2])‖) {y : ℚ_[2]}
    (h : ‖y‖ * ‖sqrtIn a‖ < 1) : ‖y‖ ≤ 1 := by
  by_contra hcon
  push Not at hcon
  have hy0 : y ≠ 0 := by
    rintro rfl
    rw [norm_zero] at hcon
    linarith
  have hinv : ‖y⁻¹‖ < 1 := by
    rw [norm_inv]
    exact inv_lt_one_of_one_lt₀ hcon
  have hle := norm_le_norm_two_of_lt_one (inv_ne_zero hy0) hinv
  rw [norm_inv, fieldUni_norm_two] at hle
  have hy0' : (0 : ℝ) < ‖y‖ := by linarith
  have hy2 : (2 : ℝ) ≤ ‖y‖ := by
    have hmul := mul_le_mul_of_nonneg_left hle (le_of_lt hy0')
    rw [mul_inv_cancel₀ (ne_of_gt hy0')] at hmul
    linarith
  have hsq := norm_sqrtIn_sq a
  rw [hna, fieldUni_norm_two] at hsq
  nlinarith [norm_nonneg (sqrtIn a)]

/-- **`√a` attains the maximal norm below `1` in `ℚ₂(√a)`**, when `v(a)` is odd and `‖a‖ = ‖2‖`.
This is the second half of the B13 uniformizer spec, the half that makes
`MarkedRecip.nu_ur_recip_uniformizer` non-vacuous at the field. -/
theorem fieldUni_sqrtIn_max (ha : ¬ IsSquare a) (hodd : Odd a.valuation)
    (hna : ‖a‖ = ‖(2 : ℚ_[2])‖) (z : ↥(quadField a)) (_hz : z ≠ 0)
    (h : ‖(z : ℚ̄₂)‖ < 1) : ‖(z : ℚ̄₂)‖ ≤ ‖sqrtIn a‖ := by
  obtain ⟨x, y, hxy⟩ := exists_repr ha z.2
  have hscalar : ∀ c : ℚ_[2], ‖(algebraMap ℚ_[2] ℚ̄₂ c)‖ < 1 →
      ‖(algebraMap ℚ_[2] ℚ̄₂ c)‖ ≤ ‖sqrtIn a‖ := by
    intro c hc
    rw [GQ2.Dyadic.Fields.norm_algebraMap] at hc ⊢
    rcases eq_or_ne c 0 with rfl | hc0
    · rw [norm_zero]
      exact norm_nonneg _
    · exact (norm_le_norm_two_of_lt_one hc0 hc).trans (fieldUni_norm_two_le_sqrtIn hna)
  have hroot : ∀ c : ℚ_[2], ‖(algebraMap ℚ_[2] ℚ̄₂ c) * sqrtIn a‖ < 1 →
      ‖(algebraMap ℚ_[2] ℚ̄₂ c) * sqrtIn a‖ ≤ ‖sqrtIn a‖ := by
    intro c hc
    rw [norm_mul, GQ2.Dyadic.Fields.norm_algebraMap] at hc ⊢
    have h1 := fieldUni_norm_le_one_of_mul_sqrtIn_lt_one hna hc
    nlinarith [norm_nonneg (sqrtIn a), norm_nonneg c]
  rcases eq_or_ne y 0 with rfl | hy
  · rw [hxy] at h ⊢
    simp only [map_zero, zero_mul, add_zero] at h ⊢
    exact hscalar x h
  rcases eq_or_ne x 0 with rfl | hx
  · rw [hxy] at h ⊢
    simp only [map_zero, zero_add] at h ⊢
    exact hroot y h
  · rw [hxy] at h ⊢
    rw [norm_add_mul_sqrtIn hodd hx hy] at h ⊢
    rw [max_lt_iff] at h
    exact max_le (hscalar x h.1) (hroot y h.2)

end Uniformizer

/-! ### §3.3 The two ramified rows whose level is zero

`ℚ₂(√−2)` and `ℚ₂(√2)` both carry an element of odd valuation whose norm is **exactly** a power
of `2`, and that is what the level asks for: the unit part of the norm is the cyclotomic value,
so it has to be `1` on the nose, not merely `≡ 1` modulo anything.

| field | `x` | `N(x)` | decomposition |
| --- | --- | --- | --- |
| `ℚ₂(√−2)` | `√−2` | `0 − (−2) = 2` | `x = 1 · √−2` |
| `ℚ₂(√2)` | `2 + √2` | `4 − 2 = 2` | `x = (1 + √2) · √2` |

The `ℚ₂(√2)` row is the one that needs a genuine factorization: `2 + √2` is not itself a `ℚ₂`
multiple of `√2`, and `√2` alone has norm `−2`, whose unit part `−1` is not `1`. -/

section RamifiedRows

variable {Rec : LocalReciprocity}

open GQ2.Dyadic.LSquare

theorem fieldUni_valuation_neg_two_odd : Odd (-2 : ℚ_[2]).valuation := by
  rw [valuation_neg, valuation_two]
  exact ⟨0, by ring⟩

theorem fieldUni_valuation_two_odd : Odd (2 : ℚ_[2]).valuation := by
  rw [valuation_two]
  exact ⟨0, by ring⟩

theorem fieldUni_norm_neg_two : ‖(-2 : ℚ_[2])‖ = ‖(2 : ℚ_[2])‖ := norm_neg 2

/-- `√a` read on the closure: `evenPolish_quadElt a 0 1` is literally `√a`. -/
@[simp] theorem fieldUni_quadElt_root_val (a : ℚ_[2]) :
    ((evenPolish_quadElt a 0 1 : ↥(quadField a)) : ℚ̄₂) = sqrtIn a := by
  rw [evenPolish_quadElt_val, map_zero, zero_add, map_one, one_mul]

/-- `√a`, as a unit of `ℚ₂(√a)`. -/
def fieldUni_rootUnit {a : ℚ_[2]} (ha : ¬ IsSquare a) : (↥(quadField a))ˣ :=
  Units.mk0 (evenPolish_quadElt a 0 1) (evenPolish_quadElt_ne_zero ha one_ne_zero)

@[simp] theorem fieldUni_rootUnit_val {a : ℚ_[2]} (ha : ¬ IsSquare a) :
    (((fieldUni_rootUnit ha : (↥(quadField a))ˣ) : ↥(quadField a)) : ℚ̄₂) = sqrtIn a := by
  rw [fieldUni_rootUnit, Units.val_mk0, fieldUni_quadElt_root_val]

/-- **`√a` is a uniformizer of `ℚ₂(√a)`**, packaged for `nu_ur_recip_of_decomp`.

⚠ [W79-HOUSE, as of `527adf51`: the headline over-reads this statement, which is the `‖·‖ < 1`
**half** of the B13 uniformizer spec and nothing more.  The maximality half is
`fieldUni_rootUnit_max` immediately below, and only the two together say "uniformizer".  §3's
own prose has it right, calling `fieldUni_sqrtIn_max` "the second half of the B13 uniformizer
spec"; and §4 puts the same headline on the maximality `Prop` for `2`, which is the correct
placement.  Read this one as "`√a` lies in the maximal ideal".] -/
theorem fieldUni_rootUnit_lt_one {a : ℚ_[2]} (ha : ¬ IsSquare a)
    (hna : ‖a‖ = ‖(2 : ℚ_[2])‖) :
    ‖(((fieldUni_rootUnit ha : (↥(quadField a))ˣ) : ↥(quadField a)) : ℚ̄₂)‖ < 1 := by
  rw [fieldUni_rootUnit_val]
  exact fieldUni_norm_sqrtIn_lt_one hna

theorem fieldUni_rootUnit_max {a : ℚ_[2]} (ha : ¬ IsSquare a) (hodd : Odd a.valuation)
    (hna : ‖a‖ = ‖(2 : ℚ_[2])‖) (z : ↥(quadField a)) (hz : z ≠ 0) (h : ‖(z : ℚ̄₂)‖ < 1) :
    ‖(z : ℚ̄₂)‖ ≤ ‖(((fieldUni_rootUnit ha : (↥(quadField a))ˣ) : ↥(quadField a)) : ℚ̄₂)‖ := by
  rw [fieldUni_rootUnit_val]
  exact fieldUni_sqrtIn_max ha hodd hna z hz h

/-- **`√−2`**, as a unit of `ℚ₂(√−2)`; its norm is `2` exactly. -/
def fieldUni_eltSqrtNegTwo : (↥KSqrtNegTwo)ˣ := fieldUni_rootUnit not_isSquare_neg_two

/-- `N_{ℚ₂(√−2)/ℚ₂}(√−2) = 0 + 2 = 1 · 2`.  The unit part is `1` **on the nose**, which is what
the level criterion needs. -/
theorem fieldUni_norm_eltSqrtNegTwo :
    normUnitsK KSqrtNegTwo fieldUni_eltSqrtNegTwo = unitEmbed (1 : ℤ_[2]ˣ) * uniformizer ^ 1 := by
  apply Units.ext
  rw [Units.val_mul, normUnitsK_val, unitEmbed_val]
  show Algebra.norm ℚ_[2] (evenPolish_quadElt (-2) 0 1)
    = algebraMap ℤ_[2] ℚ_[2] ((1 : ℤ_[2]ˣ) : ℤ_[2]) * ((uniformizer : ℚ_[2]ˣ) : ℚ_[2]) ^ 1
  rw [evenPolish_norm_quadElt not_isSquare_neg_two one_ne_zero]
  simp only [Units.val_one, map_one, uniformizer_val]
  norm_num

/-- **THE PILOT ROW IS LEVEL ZERO.**  `√−2` lies in `ker χ` (its norm has unit part `1`) and has
odd valuation, so `nu_ker_chi_le` collapses `B.r`. -/
theorem fieldUni_level_sqrtNegTwo (B : MarkedRecip Rec KSqrtNegTwo) : B.r = 0 := by
  refine fieldUni_level_eq_zero_of_decomp B fieldUni_eltSqrtNegTwo 1 fieldUni_eltSqrtNegTwo
    ?_ (by rw [zpow_one, one_mul]) ?_
    (fieldUni_rootUnit_lt_one not_isSquare_neg_two fieldUni_norm_neg_two)
    (fieldUni_rootUnit_max not_isSquare_neg_two fieldUni_valuation_neg_two_odd
      fieldUni_norm_neg_two)
  · rw [fieldUni_chi_recip_of_norm B _ 1 1 fieldUni_norm_eltSqrtNegTwo, inv_one]
  · rw [Units.val_one]
    show ‖((1 : ↥KSqrtNegTwo) : ℚ̄₂)‖ = 1
    rw [show ((1 : ↥KSqrtNegTwo) : ℚ̄₂) = 1 from rfl, norm_one]

/-- **`2 + √2`**, as a unit of `ℚ₂(√2)`; its norm is `2` exactly. -/
def fieldUni_eltSqrtTwo : (↥KSqrtTwo)ˣ :=
  Units.mk0 (evenPolish_quadElt 2 2 1) (evenPolish_quadElt_ne_zero not_isSquare_two one_ne_zero)

/-- **`1 + √2`**, the spectral unit of the factorization `2 + √2 = (1 + √2)·√2`. -/
def fieldUni_cofactorSqrtTwo : (↥KSqrtTwo)ˣ :=
  Units.mk0 (evenPolish_quadElt 2 1 1) (evenPolish_quadElt_ne_zero not_isSquare_two one_ne_zero)

/-- `N_{ℚ₂(√2)/ℚ₂}(2 + √2) = 4 − 2 = 1 · 2`. -/
theorem fieldUni_norm_eltSqrtTwo :
    normUnitsK KSqrtTwo fieldUni_eltSqrtTwo = unitEmbed (1 : ℤ_[2]ˣ) * uniformizer ^ 1 := by
  apply Units.ext
  rw [Units.val_mul, normUnitsK_val, unitEmbed_val]
  show Algebra.norm ℚ_[2] (evenPolish_quadElt 2 2 1)
    = algebraMap ℤ_[2] ℚ_[2] ((1 : ℤ_[2]ˣ) : ℤ_[2]) * ((uniformizer : ℚ_[2]ˣ) : ℚ_[2]) ^ 1
  rw [evenPolish_norm_quadElt not_isSquare_two one_ne_zero]
  simp only [Units.val_one, map_one, uniformizer_val]
  norm_num

/-- The factorization `2 + √2 = (1 + √2)·√2`, at the level of units. -/
theorem fieldUni_eltSqrtTwo_decomp :
    fieldUni_eltSqrtTwo
      = fieldUni_cofactorSqrtTwo * (fieldUni_rootUnit not_isSquare_two) ^ (1 : ℤ) := by
  apply Units.ext
  rw [zpow_one, Units.val_mul]
  apply Subtype.ext
  show algebraMap ℚ_[2] ℚ̄₂ 2 + algebraMap ℚ_[2] ℚ̄₂ 1 * sqrtIn 2
    = (algebraMap ℚ_[2] ℚ̄₂ 1 + algebraMap ℚ_[2] ℚ̄₂ 1 * sqrtIn 2)
      * (algebraMap ℚ_[2] ℚ̄₂ 0 + algebraMap ℚ_[2] ℚ̄₂ 1 * sqrtIn 2)
  rw [map_zero, map_one, zero_add, one_mul]
  linear_combination (-1 : ℚ̄₂) * sqrtIn_sq 2

/-- `‖1 + √2‖ = 1`: the cofactor is a spectral unit. -/
theorem fieldUni_norm_cofactorSqrtTwo :
    ‖((fieldUni_cofactorSqrtTwo : ↥KSqrtTwo) : ℚ̄₂)‖ = 1 := by
  show ‖(evenPolish_quadElt 2 1 1 : ↥KSqrtTwo).val‖ = 1
  rw [evenPolish_quadElt_val, norm_add_mul_sqrtIn fieldUni_valuation_two_odd one_ne_zero
    one_ne_zero, GQ2.Dyadic.Fields.norm_algebraMap, norm_one, norm_mul,
    GQ2.Dyadic.Fields.norm_algebraMap, norm_one, one_mul]
  exact max_eq_left (le_of_lt (fieldUni_norm_sqrtIn_lt_one (a := 2) rfl))

/-- **THE `ℚ₂(√2)` ROW IS LEVEL ZERO.** -/
theorem fieldUni_level_sqrtTwo (B : MarkedRecip Rec KSqrtTwo) : B.r = 0 := by
  refine fieldUni_level_eq_zero_of_decomp B fieldUni_eltSqrtTwo fieldUni_cofactorSqrtTwo
    (fieldUni_rootUnit not_isSquare_two) ?_ fieldUni_eltSqrtTwo_decomp
    fieldUni_norm_cofactorSqrtTwo (fieldUni_rootUnit_lt_one not_isSquare_two rfl)
    (fieldUni_rootUnit_max not_isSquare_two fieldUni_valuation_two_odd rfl)
  rw [fieldUni_chi_recip_of_norm B _ 1 1 fieldUni_norm_eltSqrtTwo, inv_one]

end RamifiedRows

/-! ## §4 `ℚ₂(√5)`: level zero from unramifiedness, and nothing else

At the unramified row no element of odd valuation has a norm that is a power of `2`: the residue
degree is `2`, so `v₂(N x) = 2 v_K(x)` is always even, and §3's criterion cannot be met by a norm
computation alone.  What replaces it is the scalar `2` itself: `N_{K/ℚ₂}(2) = 2^{[K:ℚ₂]}`, whose
unit part is `1`, so `2` always lies in `ker χ`, and it has `ν`-value `ofAdd(−1)` exactly when it
is a **uniformizer** — which is unramifiedness.

So the reduction is sharp and it is one line of arithmetic: at every `K` unramified over `ℚ₂`
the marked level is zero, and `ℚ₂(√5)` needs precisely `fieldUni_TwoIsUniformizer KSqrtFive`.
The tree does not carry that fact: `Fields.lean` §4's value-group work all runs under
`Odd a.valuation`, which fails at `a = 5`, and `Fields.lean:243`'s `q_K = 4` is a docstring
remark with no proof attached (contrast `qOf_KSqrt{NegTwo,Two,Ten,NegTen}`, which are theorems). -/

section Unramified

variable {K : IntermediateField ℚ_[2] ℚ̄₂} [FiniteDimensional ℚ_[2] K]
  {Rec : LocalReciprocity}

open GQ2.Dyadic.LSquare

/-- **`2` is a uniformizer of `K`** in the spectral spec of `MarkedRecip.nu_ur_recip_uniformizer`:
the statement that `K/ℚ₂` is unramified, in the repository's norm-only idiom. -/
def fieldUni_TwoIsUniformizer (K : IntermediateField ℚ_[2] ℚ̄₂) : Prop :=
  ∀ z : ↥K, z ≠ 0 → ‖(z : ℚ̄₂)‖ < 1 → ‖(z : ℚ̄₂)‖ ≤ ‖(2 : ℚ̄₂)‖

/-- `2`, as a unit of `K`. -/
def fieldUni_twoUnit (K : IntermediateField ℚ_[2] ℚ̄₂) : (↥K)ˣ :=
  Units.mk0 (2 : ↥K) two_ne_zero

@[simp] theorem fieldUni_twoUnit_val (K : IntermediateField ℚ_[2] ℚ̄₂) :
    (((fieldUni_twoUnit K : (↥K)ˣ) : ↥K) : ℚ̄₂) = (2 : ℚ̄₂) := by
  rw [fieldUni_twoUnit, Units.val_mk0]
  rfl

/-- `N_{K/ℚ₂}(2) = 2^{[K:ℚ₂]}`, unit part `1`: the scalar `2` is in `ker χ_K` at every `K`. -/
theorem fieldUni_norm_twoUnit :
    normUnitsK K (fieldUni_twoUnit K)
      = unitEmbed (1 : ℤ_[2]ˣ) * uniformizer ^ (Module.finrank ℚ_[2] K) := by
  apply Units.ext
  rw [Units.val_mul, normUnitsK_val, unitEmbed_val]
  show Algebra.norm ℚ_[2] ((2 : ↥K))
    = algebraMap ℤ_[2] ℚ_[2] ((1 : ℤ_[2]ˣ) : ℤ_[2]) * ((uniformizer : ℚ_[2]ˣ) : ℚ_[2]) ^ _
  rw [show ((2 : ↥K)) = algebraMap ℚ_[2] (↥K) 2 by rw [map_ofNat], Algebra.norm_algebraMap]
  simp only [Units.val_one, map_one, uniformizer_val, one_mul]

variable [CompactSpace (GalK K)] [TotallyDisconnectedSpace (GalK K)]

omit [CompactSpace (GalK K)] [TotallyDisconnectedSpace (GalK K)] in
/-- **Unramified forces level zero.**  The general-`K` companion of
`MarkedRecip.level_eq_zero_of_odd_finrank`: there the witness class is `rec(π·ũ)` with a scalar
correction, here it is `rec(2)` with none, because `N(2)` is a power of `2` on the nose. -/
theorem fieldUni_level_eq_zero_of_twoUniformizer (B : MarkedRecip Rec K)
    (hmax : fieldUni_TwoIsUniformizer K) : B.r = 0 := by
  refine fieldUni_level_eq_zero_of_decomp B (fieldUni_twoUnit K) 1 (fieldUni_twoUnit K)
    ?_ (by rw [zpow_one, one_mul]) ?_ ?_ ?_
  · rw [fieldUni_chi_recip_of_norm B _ 1 _ fieldUni_norm_twoUnit, inv_one]
  · rw [Units.val_one]
    show ‖((1 : ↥K) : ℚ̄₂)‖ = 1
    rw [show ((1 : ↥K) : ℚ̄₂) = 1 from rfl, norm_one]
  · rw [fieldUni_twoUnit_val]
    exact GQ2.norm_two_lt_one
  · intro z hz hlt
    rw [fieldUni_twoUnit_val]
    exact hmax z hz hlt

end Unramified

/-! ## §5 The five rows

Two rows land with **no** clause at all; `ℚ₂(√5)` lands over one named unramifiedness Prop; and
on the two procyclic rows the residual clause is restated as what §1 proves it to be, the level.

The last point is not a reformulation for its own sake.  `Main.lean:136` puts `ℚ₂(√10)` on
`.Mpc 2 1 false 1` and `Main.lean:137` puts `ℚ₂(√−10)` on `.Mpc 2 1 true 1`, and
`Main.lean:228` proves those rows valid **with `1 ≤ r`**.  So the frozen table itself says the
level is *not* zero at those two fields, and by §1 the `M0 2 0` clause of
`fieldId_genAsmBranch_sqrt{Ten,NegTen}` is exactly `B.r = 0`.  The two statements are not
contradictory in Lean (nothing in the tree pins `B.r` at those fields), but they cannot both be
about the same bundle: whichever way the arithmetic falls, one of the two rows is vacuous.  §5.2
says which, with the proof, in the module docstring's terms. -/

section Rows

variable [CompactSpace AbsGalQ2] [TotallyDisconnectedSpace AbsGalQ2] {Rec : LocalReciprocity}

/-- **THE PILOT ROW'S BRANCH DATUM, CLAUSE-FREE.**  `∃ G : GenAsmBranch, G.pres = .N0 2 0` at
`ℚ₂(√−2)` over the field's own bundle and the standing instance binders, with nothing carried:
wave 77's `hpair` is discharged by `fieldUni_level_sqrtNegTwo`. -/
theorem fieldUni_genAsmBranch_sqrtNegTwo [T2Space (GalK KSqrtNegTwo)]
    (B : MarkedRecip Rec KSqrtNegTwo) :
    ∃ G : GenAsmBranch KSqrtNegTwo B, G.pres = .N0 2 0 :=
  -- [W83-RECORDS: the producer now also names the marking; this statement keeps the
  -- weaker form, and `Instances.CanonicalRecords` restates the tied one.]
  (fieldUni_genAsmBranch_of_orientedN_level_zero 2 (le_refl 2)
    (by rw [finrank_KSqrtNegTwo]; rfl) (fieldUni_level_sqrtNegTwo B)
    (fieldId_chosenEquivN_sqrtNegTwo B)).imp fun _ hG => hG.1

/-- **THE `ℚ₂(√2)` ROW'S BRANCH DATUM, CLAUSE-FREE.**  Wave 77's `hpivot` is discharged by
`fieldUni_level_sqrtTwo`. -/
theorem fieldUni_genAsmBranch_sqrtTwo [T2Space (GalK KSqrtTwo)]
    (B : MarkedRecip Rec KSqrtTwo) :
    ∃ G : GenAsmBranch KSqrtTwo B, G.pres = .M0 3 0 :=
  (fieldUni_genAsmBranch_of_orientedM_level_zero 3 (by omega)
    (by rw [finrank_KSqrtTwo]; rfl) (fieldUni_level_sqrtTwo B)
    (fieldId_chosenEquivM_sqrtTwo B)).imp fun _ hG => hG.1

/-- **The `ℚ₂(√5)` row's branch datum**, over the unramifiedness Prop alone. -/
theorem fieldUni_genAsmBranch_sqrtFive_of_unramified [T2Space (GalK KSqrtFive)]
    (B : MarkedRecip Rec KSqrtFive) (hur : fieldUni_TwoIsUniformizer KSqrtFive) :
    ∃ G : GenAsmBranch KSqrtFive B, G.pres = .M0 2 0 :=
  (fieldUni_genAsmBranch_of_orientedM_level_zero 2 (le_refl 2)
    (by rw [finrank_KSqrtFive]; rfl) (fieldUni_level_eq_zero_of_twoUniformizer B hur)
    (fieldId_chosenEquivM_sqrtFive B)).imp fun _ hG => hG.1

/-- **What wave 77's `ℚ₂(√10)` clause says**: it is the level equation, at the very equivalence
wave 77 chose.  Read against `Main.lean:136`'s `.Mpc 2 1 false 1` (valid only with `1 ≤ r`).

⚠ [W79-HOUSE, as of `527adf51`: "it **is** the level equation" reads as an identity, and this
statement and the two below it are the forward direction only, `hpivot → B.r = 0`.  Read as
"the clause **forces** the level equation", the idiom §1 uses.  The converse does hold at these
three rows and is one application of `fieldUni_pivotM_of_level_zero` away (`α = 2` clears
`2 ≤ α`); it is simply not stated.  §5's vacuity argument needs only the forward direction, so
nothing downstream turns on this.] -/
theorem fieldUni_level_zero_of_hpivot_sqrtTen [T2Space (GalK KSqrtTen)]
    (B : MarkedRecip Rec KSqrtTen)
    (hpivot : IsUnit (Multiplicative.toAdd
      (nuUrKTwo B ((fieldId_chosenEquivM_sqrtTen B).1 (dmC 2 0))))) : B.r = 0 :=
  fieldUni_level_zero_of_pivotM B _ hpivot

/-- **What wave 77's `ℚ₂(√−10)` clause says**, likewise, against `Main.lean:137`. -/
theorem fieldUni_level_zero_of_hpivot_sqrtNegTen [T2Space (GalK KSqrtNegTen)]
    (B : MarkedRecip Rec KSqrtNegTen)
    (hpivot : IsUnit (Multiplicative.toAdd
      (nuUrKTwo B ((fieldId_chosenEquivM_sqrtNegTen B).1 (dmC 2 0))))) : B.r = 0 :=
  fieldUni_level_zero_of_pivotM B _ hpivot

/-- **The `ℚ₂(√5)` clause, likewise**, so all five rows read in the same currency. -/
theorem fieldUni_level_zero_of_hpivot_sqrtFive [T2Space (GalK KSqrtFive)]
    (B : MarkedRecip Rec KSqrtFive)
    (hpivot : IsUnit (Multiplicative.toAdd
      (nuUrKTwo B ((fieldId_chosenEquivM_sqrtFive B).1 (dmC 2 0))))) : B.r = 0 :=
  fieldUni_level_zero_of_pivotM B _ hpivot

end Rows

end

/-! ## §6 Axiom pins

Two sets, both already committed, and the split is exactly where wave 77 left it.

* Everything about the **level** — §1's two equivalences, §3's criterion and the quadratic
  uniformizer, §4's unramified reduction, and the two fields' level equations — is at the
  standard three, `propext, Classical.choice, Quot.sound`.  So the arithmetic discharged here
  costs no axiom.
  ⚠ [W79-HOUSE, as of `527adf51`: machine-checked, and the 23 declarations the dashes enumerate
  do all print exactly the standard three.  But "everything about the level" is too wide: §5's
  `fieldUni_level_zero_of_hpivot_sqrt{Five,Ten,NegTen}` conclude `B.r = 0` and print **seven**
  axioms each, the four extras coming from the chosen equivalence `fieldId_chosenEquivM_*`, not
  from the level argument.  The follow-on sentence stays true as written; the quantifier wants
  "every level statement proved from the field arithmetic here".]
* The **`M`-row producers and branch data** carry `peripheralCyclotomicAction`, inherited from
  `marked_matching_certificate_KTwoM_of_level_zero` (whose B8 transport supplies the M3 unit
  scaling that `mMixHypothesis` supplied on the non-level-zero route).  The `N` row does not
  carry it, matching wave 77's split.  The `√−2` pilot datum is therefore at the standard three
  plus the even route's endpoint set, and nothing else. -/

section AxiomPins

-- §1 the clause is the level
#print axioms fieldUni_level_eq_zero_of_chiKer
#print axioms fieldUni_level_eq_zero_of_chiKerTwo
#print axioms fieldUni_level_zero_of_pivotM
#print axioms fieldUni_level_zero_of_pairN
#print axioms fieldUni_chiKerUnimodularM
#print axioms fieldUni_chiKerUnimodularN
#print axioms fieldUni_pivotM_of_level_zero
#print axioms fieldUni_pairN_of_level_zero
#print axioms fieldUni_pivotM_iff_level_zero
#print axioms fieldUni_pairN_iff_level_zero

-- §2 the level-zero producers
#print axioms fieldUni_genAsmBranch_of_orientedM_level_zero
#print axioms fieldUni_genAsmBranch_of_orientedN_level_zero

-- §3 the level at a field
#print axioms fieldUni_chi_recip_of_norm
#print axioms fieldUni_level_eq_zero_of_decomp
#print axioms fieldUni_norm_sqrtIn_lt_one
#print axioms fieldUni_norm_two_le_sqrtIn
#print axioms fieldUni_sqrtIn_max
#print axioms fieldUni_norm_eltSqrtNegTwo
#print axioms fieldUni_norm_eltSqrtTwo
#print axioms fieldUni_eltSqrtTwo_decomp
#print axioms fieldUni_norm_cofactorSqrtTwo
#print axioms fieldUni_level_sqrtNegTwo
#print axioms fieldUni_level_sqrtTwo

-- §4 the unramified reduction
#print axioms fieldUni_norm_twoUnit
#print axioms fieldUni_level_eq_zero_of_twoUniformizer

-- §5 the five rows
#print axioms fieldUni_genAsmBranch_sqrtNegTwo
#print axioms fieldUni_genAsmBranch_sqrtTwo
#print axioms fieldUni_genAsmBranch_sqrtFive_of_unramified
#print axioms fieldUni_level_zero_of_hpivot_sqrtFive
#print axioms fieldUni_level_zero_of_hpivot_sqrtTen
#print axioms fieldUni_level_zero_of_hpivot_sqrtNegTen

-- the committed statements consumed, for the side-by-side
#print axioms GQ2.Dyadic.marked_matching_certificate_KTwoM_of_level_zero
#print axioms GQ2.Dyadic.marked_matching_certificate_KTwoN_of_level_zero
#print axioms GQ2.Dyadic.FieldBranchId.fieldId_genAsmBranch_sqrtNegTwo
#print axioms GQ2.Dyadic.FieldBranchId.fieldId_genAsmBranch_sqrtTwo

end AxiomPins

end GQ2.Dyadic.FieldUnimod
