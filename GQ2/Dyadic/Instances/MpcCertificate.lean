/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Opus-5
-/
import GQ2.Dyadic.GeneralAssembly
import GQ2.Dyadic.Instances.Cores
import GQ2.Dyadic.Instances.FieldUnimodularity

/-!
# W79-MPC: the marked-core certificate producer for the procyclic `M` rows

## The ticket

`docs/dyadic/w78-unimod-note.md` §6 item 2.  Wave 78 proved that on an `M0` or `N0` row the
residual marked-data clause **is** the level `B.r = 0`, and that at `ℚ₂(√10)` and `ℚ₂(√−10)` the
level is `1`.  So wave 77's branch data at those two fields, built at `pres = .M0 2 0`, are
theorems with unsatisfiable hypotheses; `Main.lean:136-137` puts both fields on the
`.Mpc 2 1 _ 1` rows, whose `FieldBranchSelector.Matches` clause demands `r = Q.r`.  The tree had
no marked-core certificate producer for that shape: `marked_matching_certificate_KTwoM`/`KTwoN`
and their level-zero variants serve the `M0` and `N0` shapes only.

## What the `Mpc` shape actually needs

The core is **not** new.  `GeneralAssembly.genAsmCore` sends `.Mpc α r ε η h` to `DM α h`, the
same group the `.M0 α h` row uses, and `LabuteInterface.BranchData.CoreCertificate` gives the
two rows the same certificate type.  What differs is the **marking**: the branch datum's `nuP`
field at a procyclic row is `MProcyclicCore.mpcNu α r p`, whose ν-exponent vector
`(ν(μ₃), ν(μ₂), ν(μ₁), ν(μ₀)) = (1, s, p, −m·s)` carries `s = 2^r` at the boundary letter `C̄₀`,
where the compact marking `mNu` carries `1`.  A `MarkedCoreCertificateM` is by definition a
normalization of the transported marking to `nuM`, whose `C̄₀`-value is a **unit**; wave 78's
`fieldUni_pivotM_iff_level_zero` says that is the same thing as `B.r = 0`.  Hence:

> **No `MarkedCoreCertificateM` can exist at a field of level `r ≥ 1`.**  The procyclic rows
> need a certificate against `mpcNu`, and that is what `MarkedCoreCertificateMpc` below is.

## What is proved here

§3's normalization `mpcCert_markedMatching` is the level-`r` analogue of MC5's
`mMarkedMatching`, and it runs on exactly the committed correction moves, in the same order as
`mMixHypothesis_of_scaling`:

* **M3** (`mScalingHypothesis_zero`, a theorem at `h = 0`) scales the `C̄₀`-value by any unit, so
  it normalizes `ν'(C̄₀)` to `2^r` **iff** that value has 2-adic valuation exactly `r`;
* **M2** (`dmTauDEquiv`, exact) shifts `ν'(D̄)` by multiples of `ν'(C̄₀) = 2^r`, so it reaches `1`
  **iff** `ν'(D̄) ≡ 1 (mod 2^r)`;
* **M5** (`mMixFamily_coreMix`, exact at `α ≥ 2`) shifts `ν'(B̄)` by multiples of the same pivot,
  so it reaches `p` **iff** `ν'(B̄) ≡ p (mod 2^r)`;
* the `Ā`-row is then forced by the abelianized relation (`nu_dmA_eq`), and it lands on
  `−2^{α−1}·2^r = −m·s`, which is `mpcNuExp` slot `0` on the nose.

The three "iff"s are the content of `MpcMarkedData`, §2's named clause.  At `r = 0` its first
component is `IsUnit (ν'(C̄₀))`, i.e. the committed `hpivot`, so `MpcMarkedData` is the honest
generalization of the compact clause and not a new kind of assumption.

**The one input the tree does not carry.**  The three congruences do not follow from the level
alone.  At level `r` the level fixes only that `ν'` is `2^r`-divisible on `ker χ`; the 2-adic
valuation of `ν'(C̄₀)` and the residues of `ν'(D̄)` and `ν'(B̄)` modulo `2^r` are separate
invariants of the χ-preserving action (M3 cannot change a valuation, M2 and M5 shift only by
multiples of the pivot).  At `r = 0` all three are vacuous or automatic (`2^0 ℤ₂ = ℤ₂` makes the
last two trivial, and `isUnit_nu_dmC_of_chiKer` supplies the first from the level), which is why
the compact rows needed nothing beyond `B.r = 0`.  **At `r ≥ 1` they are genuine extra
arithmetic**, and §6 carries them, per field, as one named `Prop`.

Their shapes are not arbitrary: `FieldBranchSelector.Matches` at an `.Mpc β r ε η` row asks for
`r = Q.r`, for `negOneVal = ε·2^{r−1} (mod 2^r)`, and for `IsEtaFor Q.datum u η`.  The `B̄`
congruence of `MpcMarkedData` is the second of those read on the core (`χ_M(B̄) = −1`), and the
`D̄` congruence is the marking half of the third (`D̄` is the χ-generator).

## Layout

* §1 the target marking `mpcCert_nuMpc` (`mpcNu` through the `Ztwo` seam) and its four rows;
* §2 the two named clauses, `MpcChiKerLevel` and `MpcMarkedData`, and the χ-kernel invariance
  that makes the first survive a change of variables;
* §3 the normalization `mpcCert_markedMatching`;
* §4 `MarkedCoreCertificateMpc` and the producers, ending at
  `mpcCert_marked_matching_certificate_KTwoMpc`;
* §5 the realization and the branch datum at `pres = .Mpc α r ε η 0`;
* §6 the two fields;
* §7 axiom pins.

No `sorry`, no new axiom, no `native_decide`, no `maxHeartbeats`, no `maxRecDepth`.
-/

namespace GQ2.Dyadic.Instances.MpcCert

open GQ2 GQ2.Dyadic GQ2.Dyadic.MarkedCore Multiplicative
open GQ2.Dyadic.Instances.MProcyclicCore GQ2.Dyadic.Instances.NuWitness
open GQ2.Dyadic.FieldBranchId GQ2.Dyadic.FieldUnimod GQ2.Dyadic.Fields

noncomputable section

/-! ## §1 The target marking

`GenAsmBranch.nuP` at a procyclic row is `mpcNu α r p`, the `Ztwo`-valued witness of
`Instances/Cores.lean` §10; the marked-core layer speaks `Multiplicative ℤ_[2]`.  This section
is the seam and the four generator rows, in the `toAdd` spelling the frame uses. -/

section Target

variable (α r pp : ℕ)

/-- **The procyclic-`M` marking in marked-core spelling**: `mpcNu` read through the boundary
seam `ztwoIota`.  This is the `Mpc` counterpart of `MarkedCore.nuM`, and it is the marking the
row's own word certificate consumes (`MProcyclicCore.mpcCompat`). -/
def mpcCert_nuMpc (hα : 1 ≤ α) :
    ContinuousMonoidHom (DM α 0 : Type) (Multiplicative ℤ_[2]) :=
  ⟨ztwoIota.toMulEquiv.toMonoidHom.comp (mpcNu α r pp hα).toMonoidHom,
    ztwoIota.continuous_toFun.comp (mpcNu α r pp hα).continuous_toFun⟩

/-- The seam, stated so the branch datum's `hnuIota` obligation is `rfl`. -/
theorem mpcCert_ztwoIota_mpcNu (hα : 1 ≤ α) (x : (DM α 0 : Type)) :
    ztwoIota (mpcNu α r pp hα x) = mpcCert_nuMpc α r pp hα x := rfl

/-- The seam takes `ztwoOne ^ e` to `ofAdd e`. -/
theorem mpcCert_toAdd_ztwoIota_zpow (e : ℤ) :
    toAdd (ztwoIota (ztwoOne ^ e)) = (e : ℤ_[2]) := by
  rw [map_zpow, ztwoIota_ztwoOne]
  simp

/-- The marking at a marked generator is its `mpcNuExp` entry. -/
theorem mpcCert_toAdd_nuMpc_gen (hα : 1 ≤ α) (i : Fin (coreRank 0)) :
    toAdd (mpcCert_nuMpc α r pp hα (dmGen α 0 i)) = ((mpcNuExp α r pp i : ℤ) : ℤ_[2]) := by
  show toAdd (ztwoIota (mpcNu α r pp hα (dmGen α 0 i))) = _
  rw [mpcNu, dmNu_dmGen, mpcCert_toAdd_ztwoIota_zpow]

@[simp] theorem mpcCert_toAdd_nuMpc_dmA (hα : 1 ≤ α) :
    toAdd (mpcCert_nuMpc α r pp hα (dmA α 0)) = -((2 : ℤ_[2]) ^ (α - 1) * 2 ^ r) := by
  rw [show dmA α 0 = dmGen α 0 0 from rfl, mpcCert_toAdd_nuMpc_gen, mpcNuExp_zero]
  push_cast [m, s]
  ring

@[simp] theorem mpcCert_toAdd_nuMpc_dmB (hα : 1 ≤ α) :
    toAdd (mpcCert_nuMpc α r pp hα (dmB α 0)) = (pp : ℤ_[2]) := by
  rw [show dmB α 0 = dmGen α 0 1 from rfl, mpcCert_toAdd_nuMpc_gen, mpcNuExp_one]
  push_cast
  ring

@[simp] theorem mpcCert_toAdd_nuMpc_dmC (hα : 1 ≤ α) :
    toAdd (mpcCert_nuMpc α r pp hα (dmC α 0)) = (2 : ℤ_[2]) ^ r := by
  rw [show dmC α 0 = dmGen α 0 2 from rfl, mpcCert_toAdd_nuMpc_gen, mpcNuExp_two]
  push_cast [s]
  ring

@[simp] theorem mpcCert_toAdd_nuMpc_dmD (hα : 1 ≤ α) :
    toAdd (mpcCert_nuMpc α r pp hα (dmD α 0)) = 1 := by
  rw [show dmD α 0 = dmGen α 0 3 from rfl, mpcCert_toAdd_nuMpc_gen, mpcNuExp_three]
  push_cast
  ring

end Target

/-! ## §2 The two named clauses

`MpcChiKerLevel` is the level in the shape the core reads it (the `nu_ker_chi_le` half,
transported), and it is what makes the other two clauses *invariant* under the correction moves.
`MpcMarkedData` is the level-`r` replacement for `hpivot`. -/

section Clauses

variable (α r pp : ℕ) (nu' : ContinuousMonoidHom (DM α 0 : Type) (Multiplicative ℤ_[2]))

/-- **The level, read on the core**: the transported marking is `2^r`-divisible on `ker χ_M`.
This is `MarkedRecip.nu_ker_chi_le` pulled back along an oriented equivalence (§6's
`mpcCert_chiKerLevel_of_level`). -/
def MpcChiKerLevel : Prop :=
  ∀ z : (DM α 0 : Type), chiM α 0 z = 1 → ∃ y : ℤ_[2], toAdd (nu' z) = 2 ^ r * y

/-- **The level-`r` marked data**, the `Mpc` replacement for the compact rows' `hpivot`:

* the pivot `C̄₀` carries a value of 2-adic valuation exactly `r`;
* the χ-generator `D̄` carries `1` modulo `2^r`;
* the sign letter `B̄` carries `p` modulo `2^r`.

At `r = 0` the first clause is `IsUnit (toAdd (ν'(C̄₀)))` and the other two are vacuous, so this
is the honest generalization of the committed clause and not a new species of assumption. -/
def MpcMarkedData : Prop :=
  (∃ γ : ℤ_[2]ˣ, toAdd (nu' (dmC α 0)) = (γ : ℤ_[2]) * 2 ^ r) ∧
    (∃ w : ℤ_[2], toAdd (nu' (dmD α 0)) = 1 + 2 ^ r * w) ∧
      ∃ w : ℤ_[2], toAdd (nu' (dmB α 0)) = (pp : ℤ_[2]) + 2 ^ r * w

variable {α r pp nu'}

/-- **The level is an invariance principle.**  A χ-preserving automorphism moves any value of
the marking only inside `2^r ℤ₂`: the ratio `Ψ g · g⁻¹` lies in `ker χ_M`.  This is what lets
the correction algorithm below apply M3 first, which says nothing about the `B̄` and `D̄` rows,
without losing their residues. -/
theorem mpcCert_shift_mem (hlev : MpcChiKerLevel α r nu')
    {Ψ : ContinuousMulEquiv (DM α 0 : Type) (DM α 0 : Type)}
    (hΨ : ∀ x, chiM α 0 (Ψ x) = chiM α 0 x) (g : (DM α 0 : Type)) :
    ∃ y : ℤ_[2], toAdd (nu' (Ψ g)) = toAdd (nu' g) + 2 ^ r * y := by
  obtain ⟨y, hy⟩ := hlev (Ψ g * g⁻¹) (by rw [map_mul, map_inv, hΨ, mul_inv_cancel])
  refine ⟨y, ?_⟩
  rw [map_mul, map_inv, toAdd_mul, toAdd_inv] at hy
  linear_combination hy

/-- The `D̄` residue survives a χ-preserving change of variables. -/
theorem mpcCert_dmD_shift (hlev : MpcChiKerLevel α r nu')
    (hD : ∃ w : ℤ_[2], toAdd (nu' (dmD α 0)) = 1 + 2 ^ r * w)
    {Ψ : ContinuousMulEquiv (DM α 0 : Type) (DM α 0 : Type)}
    (hΨ : ∀ x, chiM α 0 (Ψ x) = chiM α 0 x) :
    ∃ w : ℤ_[2], toAdd (nu' (Ψ (dmD α 0))) = 1 + 2 ^ r * w := by
  obtain ⟨w, hw⟩ := hD
  obtain ⟨y, hy⟩ := mpcCert_shift_mem hlev hΨ (dmD α 0)
  exact ⟨w + y, by rw [hy, hw]; ring⟩

/-- The `B̄` residue survives a χ-preserving change of variables. -/
theorem mpcCert_dmB_shift (hlev : MpcChiKerLevel α r nu')
    (hB : ∃ w : ℤ_[2], toAdd (nu' (dmB α 0)) = (pp : ℤ_[2]) + 2 ^ r * w)
    {Ψ : ContinuousMulEquiv (DM α 0 : Type) (DM α 0 : Type)}
    (hΨ : ∀ x, chiM α 0 (Ψ x) = chiM α 0 x) :
    ∃ w : ℤ_[2], toAdd (nu' (Ψ (dmB α 0))) = (pp : ℤ_[2]) + 2 ^ r * w := by
  obtain ⟨w, hw⟩ := hB
  obtain ⟨y, hy⟩ := mpcCert_shift_mem hlev hΨ (dmB α 0)
  exact ⟨w + y, by rw [hy, hw]; ring⟩

end Clauses

/-! ## §3 The level-`r` normalization

MC5's `mMarkedMatching` runs M3 → handles → M2 → M5 and lands on `nuM`.  The same four moves,
with the pivot normalized to `2^r` instead of to `1`, land on `mpcNu`.  Handles are absent
(`h = 0`), and the `Ā`-row is forced rather than moved. -/

section Normalization

/-- **The `Mpc` marked-matching reduction.**  A transported marking of level `r` carrying the
level-`r` marked data is χ-preservingly equivalent to the canonical procyclic marking
`mpcNu α r p`.  This is the `Mpc` twin of `MarkedCore.mMarkedMatching`, and every move it uses
is committed: M3 is `mScalingHypothesis_zero` (a theorem at `h = 0`), M2 is `dmTauDEquiv`, M5 is
`mMixFamily_coreMix` at `α ≥ 2`, and the `Ā`-row is `nu_dmA_eq`. -/
theorem mpcCert_markedMatching {α : ℕ} (r pp : ℕ) (hα : 2 ≤ α) (hα1 : 1 ≤ α)
    (nu' : ContinuousMonoidHom (DM α 0 : Type) (Multiplicative ℤ_[2]))
    (hlev : MpcChiKerLevel α r nu') (hdata : MpcMarkedData α r pp nu') :
    ∃ u : ContinuousMulEquiv (DM α 0 : Type) (DM α 0 : Type),
      (∀ x, chiM α 0 (u x) = chiM α 0 x) ∧
        ∀ x, nu' (u x) = mpcCert_nuMpc α r pp hα1 x := by
  obtain ⟨⟨γ, hγ⟩, hD, hB⟩ := hdata
  -- Step 1 (M3/S2): normalize the pivot to `2^r`.  The other rows may move arbitrarily, but
  -- §2's invariance keeps their residues.
  obtain ⟨Ψs, hsChi, hsC⟩ := mScalingHypothesis_zero α γ⁻¹
  set nu2 : ContinuousMonoidHom (DM α 0 : Type) (Multiplicative ℤ_[2]) :=
    nu'.comp (autHom Ψs) with hnu2
  have hc2 : toAdd (nu2 (dmC α 0)) = 2 ^ r := by
    show toAdd (nu' (Ψs (dmC α 0))) = _
    rw [hsC nu', hγ, ← mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_mul]
  obtain ⟨wD, hwD⟩ := mpcCert_dmD_shift hlev hD hsChi
  obtain ⟨wB, hwB⟩ := mpcCert_dmB_shift hlev hB hsChi
  have hwD2 : toAdd (nu2 (dmD α 0)) = 1 + 2 ^ r * wD := hwD
  have hwB2 : toAdd (nu2 (dmB α 0)) = (pp : ℤ_[2]) + 2 ^ r * wB := hwB
  have hone_ne_three : (1 : Fin (coreRank 0)) ≠ 3 := fun hh => by
    have hv := congrArg Fin.val hh
    rw [coreVal_one, coreVal_three] at hv
    omega
  -- Step 2 (exact M2): clear `D̄` against the pivot.
  set k : ℤ_[2] := -wD with hk
  set nu3 : ContinuousMonoidHom (DM α 0 : Type) (Multiplicative ℤ_[2]) :=
    nu2.comp (autHom (dmTauDEquiv α 0 k)) with hnu3
  have hgen3 : ∀ i : Fin (coreRank 0),
      nu3 (dmGen α 0 i) = nu2 (tauDMark (isProP_DM α 0) k (dmGen α 0) i) := fun i => by
    show nu2 (dmTauDEquiv α 0 k (dmGen α 0 i)) = _
    rw [dmTauDEquiv_gen]
  have hc3 : toAdd (nu3 (dmC α 0)) = 2 ^ r := by
    rw [show dmC α 0 = dmGen α 0 2 from rfl, hgen3, tauDMark_two]
    exact hc2
  have hd3 : toAdd (nu3 (dmD α 0)) = 1 := by
    rw [show dmD α 0 = dmGen α 0 3 from rfl, hgen3, tauDMark_three, map_mul, toAdd_mul,
      toAdd_map_zpowZtwo (isProP_DM α 0) nu2, show dmGen α 0 2 = dmC α 0 from rfl, hc2,
      show dmGen α 0 3 = dmD α 0 from rfl, hwD2, hk]
    ring
  have hb3 : toAdd (nu3 (dmB α 0)) = (pp : ℤ_[2]) + 2 ^ r * wB := by
    rw [show dmB α 0 = dmGen α 0 1 from rfl, hgen3, tauDMark_of_ne _ _ _ hone_ne_three]
    exact hwB2
  -- Step 3 (exact M5): clear `B̄` against the same pivot.
  set b : ℤ_[2] := -wB with hb
  obtain ⟨Ψ5, h5Chi, h5Frame⟩ := mMixFamily_coreMix α 0 hα b
  refine ⟨Ψ5.trans ((dmTauDEquiv α 0 k).trans Ψs), fun x => ?_, ?_⟩
  · show chiM α 0 (Ψs (dmTauDEquiv α 0 k (Ψ5 x))) = chiM α 0 x
    rw [hsChi, chiM_dmTauDEquiv, h5Chi]
  · intro x
    have hext : nu3.comp (autHom Ψ5) = mpcCert_nuMpc α r pp hα1 := by
      refine dm_hom_ext _ _ fun i => ?_
      have hrow := congrFun (h5Frame nu3) i
      rw [nuFrame_apply, nFrameMixX1] at hrow
      change nu3 (Ψ5 (dmGen α 0 i)) = mpcCert_nuMpc α r pp hα1 (dmGen α 0 i)
      refine Multiplicative.toAdd.injective ?_
      rcases mCoreIdx_cases i with rfl | rfl | rfl | rfl
      · rw [hrow, Function.update_of_ne nCoreZero_ne_one, nuFrame_apply,
          show dmGen α 0 0 = dmA α 0 from rfl, mpcCert_toAdd_nuMpc_dmA]
        have hA := nu_dmA_eq α 0 hα1 nu3
        rw [hc3] at hA
        rw [hA]
        ring
      · rw [hrow, Function.update_self, nuFrame_apply, nuFrame_apply,
          show dmGen α 0 1 = dmB α 0 from rfl, show dmGen α 0 2 = dmC α 0 from rfl,
          hc3, hb3, hb, mpcCert_toAdd_nuMpc_dmB]
        ring
      · rw [hrow, Function.update_of_ne nCoreTwo_ne_one, nuFrame_apply,
          show dmGen α 0 2 = dmC α 0 from rfl, hc3, mpcCert_toAdd_nuMpc_dmC]
      · rw [hrow, Function.update_of_ne nCoreThree_ne_one, nuFrame_apply,
          show dmGen α 0 3 = dmD α 0 from rfl, hd3, mpcCert_toAdd_nuMpc_dmD]
    exact DFunLike.congr_fun hext x

end Normalization

/-! ## §4 The certificate and its producers

`MarkedCoreCertificateMpc` is `MarkedCoreCertificateM` with `nuM` replaced by `mpcNu`: same
abstract Demushkin isomorphism, same orientation clause, same marking-correcting automorphism,
different normal form for the marking.  The two are *not* interchangeable; see the module
docstring. -/

section Certificate

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- The marking of the abstract core pulled back along an abstract equivalence, the object the
change of variables is stated against (`fieldUni_nuPullbackM` with the equivalence unbundled). -/
def mpcCert_transport {α : ℕ} (nuG : G →* Multiplicative ℤ_[2])
    (f : ContinuousMulEquiv (DM α 0 : Type) G)
    (hcont : Continuous fun x : (DM α 0 : Type) => nuG (f x)) :
    ContinuousMonoidHom (DM α 0 : Type) (Multiplicative ℤ_[2]) where
  toFun x := nuG (f x)
  map_one' := by rw [map_one, map_one]
  map_mul' x y := by rw [map_mul, map_mul]
  continuous_toFun := hcont

/-- **The marked-core certificate for the procyclic `M_α` rows.**  The `Mpc` twin of
`MarkedCore.MarkedCoreCertificateM`; the core group is the same `DM α 0`, and only the marking's
normal form differs. -/
structure MarkedCoreCertificateMpc (α r pp : ℕ) (hα : 1 ≤ α)
    (chiG : G →* ℤ_[2]ˣ) (nuG : G →* Multiplicative ℤ_[2]) where
  /-- Item 1: the abstract Demushkin isomorphism. -/
  abstractEquiv : ContinuousMulEquiv (DM α 0 : Type) G
  /-- Item 2: the intrinsic orientation matches the canonical one through the isomorphism. -/
  orientation : ∀ x, chiG (abstractEquiv x) = chiM α 0 x
  /-- Item 3a: the marking-correcting automorphism. -/
  correction : ContinuousMulEquiv (DM α 0 : Type) (DM α 0 : Type)
  /-- Item 3b: the correction preserves the canonical orientation. -/
  correction_chi : ∀ x, chiM α 0 (correction x) = chiM α 0 x
  /-- Item 3c: the corrected isomorphism matches the **procyclic** marking. -/
  correction_nu : ∀ x, nuG (abstractEquiv (correction x)) = mpcCert_nuMpc α r pp hα x

omit [IsTopologicalGroup G] in
/-- **Certificate production, `Mpc`-side.**  The exact analogue of
`marked_matching_certificate_M`, with `MMixHypothesis` gone (M3 is a theorem at `h = 0`) and the
pivot datum replaced by the level plus the level-`r` marked data. -/
theorem mpcCert_marked_matching_certificate_Mpc {α : ℕ} (r pp : ℕ) (hα : 2 ≤ α) (hα1 : 1 ≤ α)
    (chiG : G →* ℤ_[2]ˣ) (nuG : G →* Multiplicative ℤ_[2])
    (f : ContinuousMulEquiv (DM α 0 : Type) G)
    (horient : ∀ x, chiG (f x) = chiM α 0 x)
    (hcont : Continuous fun x : (DM α 0 : Type) => nuG (f x))
    (hlev : MpcChiKerLevel α r (mpcCert_transport nuG f hcont))
    (hdata : MpcMarkedData α r pp (mpcCert_transport nuG f hcont)) :
    Nonempty (MarkedCoreCertificateMpc α r pp hα1 chiG nuG) := by
  obtain ⟨u, huchi, hunu⟩ := mpcCert_markedMatching r pp hα hα1 _ hlev hdata
  exact ⟨⟨f, horient, u, huchi, fun x => hunu x⟩⟩

end Certificate

/-! ## §5 The direct `G_K(2)` producer, the realization, and the branch datum -/

section KTwo

variable {Rec : LocalReciprocity}
  {K : IntermediateField ℚ_[2] (AlgebraicClosure ℚ_[2])} [FiniteDimensional ℚ_[2] K]
  [CompactSpace AbsGalQ2] [TotallyDisconnectedSpace AbsGalQ2]
  [CompactSpace (GalK K)] [TotallyDisconnectedSpace (GalK K)]

/-- The procyclic certificate read directly at the two canonical characters on `G_K(2)`, the
`Mpc` analogue of `MarkedCoreCertificateKTwoM`. -/
abbrev MarkedCoreCertificateKTwoMpc (B : MarkedRecip Rec K) (α r pp : ℕ) (hα : 1 ≤ α) :=
  MarkedCoreCertificateMpc α r pp hα (chiCycKTwo (K := K)).toMonoidHom
    (nuUrKTwo B).toMonoidHom

omit [CompactSpace AbsGalQ2] [TotallyDisconnectedSpace AbsGalQ2] in
/-- **THE PROCYCLIC PRODUCER.**  The `Mpc` counterpart of `marked_matching_certificate_KTwoM`,
stated at an oriented equivalence and the two level-`r` clauses on the pulled-back marking.
This is the declaration wave 78 §6 item 2 reported the tree as lacking. -/
theorem mpcCert_marked_matching_certificate_KTwoMpc (B : MarkedRecip Rec K) {α : ℕ} (r pp : ℕ)
    (hα : 2 ≤ α) (hα1 : 1 ≤ α)
    (e : OrientedContinuousMulEquiv (chiM α 0) (chiCycKTwo (K := K)))
    (hlev : MpcChiKerLevel α r (fieldUni_nuPullbackM B e))
    (hdata : MpcMarkedData α r pp (fieldUni_nuPullbackM B e)) :
    Nonempty (MarkedCoreCertificateKTwoMpc B α r pp hα1) := by
  obtain ⟨u, huchi, hunu⟩ := mpcCert_markedMatching r pp hα hα1 (fieldUni_nuPullbackM B e)
    hlev hdata
  exact ⟨⟨e.1, e.2, u, huchi, fun x => hunu x⟩⟩

/-- Turn a procyclic marked-core certificate into the common realization, at the row's own
canonical `Ztwo` marking `mpcNu`.  The `Mpc` analogue of
`MarkedCoreRealization.ofCertificateM`. -/
def mpcCert_realization {B : MarkedRecip Rec K} {α r pp : ℕ} {hα : 1 ≤ α}
    (C : MarkedCoreCertificateKTwoMpc B α r pp hα) :
    MarkedCoreRealization (K := K) (B := B) (DM α 0) (mpcNu α r pp hα) where
  equiv := C.correction.trans C.abstractEquiv
  nu_equiv := fun x => (C.correction_nu x).symm

/-- **THE PROCYCLIC BRANCH DATUM.**  A `GenAsmBranch` sitting on the `.Mpc α r ε η 0` row, from
an oriented equivalence and the two level-`r` clauses.  The marking triple is discharged at the
row's own canonical marking (`mpcNu_surjective`, and the seam is `rfl`), so nothing about `nuP`
is carried. -/
theorem mpcCert_genAsmBranch_of_orientedMpc {B : MarkedRecip Rec K} {α : ℕ} (r pp : ℕ)
    (epsilon : Bool) (eta : Words.Mpc.EtaDisplay) (hα : 2 ≤ α) (hα1 : 1 ≤ α)
    (hdeg : Module.finrank ℚ_[2] K = (SelectedPresentation.Mpc α r epsilon eta 0).degree)
    (e : OrientedContinuousMulEquiv (chiM α 0) (chiCycKTwo (K := K)))
    (hlev : MpcChiKerLevel α r (fieldUni_nuPullbackM B e))
    (hdata : MpcMarkedData α r pp (fieldUni_nuPullbackM B e)) :
    ∃ G : GenAsmBranch K B, G.pres = .Mpc α r epsilon eta 0 := by
  obtain ⟨C⟩ := mpcCert_marked_matching_certificate_KTwoMpc B r pp hα hα1 e hlev hdata
  exact ⟨{ pres := .Mpc α r epsilon eta 0, hdeg := hdeg, nuP := mpcNu α r pp hα1,
           hnuP := mpcNu_surjective α r pp hα1, realization := mpcCert_realization C }, rfl⟩

end KTwo

/-! ## §6 The two procyclic fields

`ℚ₂(√10)` sits on `.Mpc 2 1 false .one 0` and `ℚ₂(√−10)` on `.Mpc 2 1 true .one 0`
(`Main.lean:136-137`, `GeneralAssembly.genAsm_core_sqrt{Ten,NegTen}`), with `p false 1 = 0` and
`p true 1 = 1`.  Wave 77's range identity at each field is untouched by wave 78's correction and
supplies the oriented equivalence; what the tree does not carry is the level and the three
congruences, so each field costs exactly one named `Prop`. -/

section Fields

variable {K : IntermediateField ℚ_[2] (AlgebraicClosure ℚ_[2])} [FiniteDimensional ℚ_[2] K]
  [CompactSpace (GalK K)] [TotallyDisconnectedSpace (GalK K)]
  {Rec : LocalReciprocity}

/-- **The level, transported to `G_K(2)`**: `nu_ker_chi_le` read at the maximal pro-`2`
quotient, the `≤`-half twin of wave 78's `fieldUni_level_eq_zero_of_chiKerTwo`. -/
theorem mpcCert_nu_le_of_chiKerTwo (B : MarkedRecip Rec K)
    {q : maxProPQuotient 2 (GalK K)} (hchi : chiCycKTwo (K := K) q = 1) :
    ∃ y : ℤ_[2], toAdd (nuUrKTwo B q) = 2 ^ B.r * y := by
  obtain ⟨g, rfl⟩ := maxProPMk_surjective (p := 2) (G := GalK K) q
  rw [chiCycKTwo_maxProPMk, ← chiCycKAb_toAbK] at hchi
  rw [nuUrKTwo_maxProPMk]
  exact B.nu_ker_chi_le _ hchi

/-- **The bundle's level gives the core's level clause.**  So `MpcChiKerLevel` is not an extra
assumption beyond `B.r = r`: it is that equation, read through the equivalence. -/
theorem mpcCert_chiKerLevel_of_level (B : MarkedRecip Rec K) {α r : ℕ} (hr : B.r = r)
    (e : OrientedContinuousMulEquiv (chiM α 0) (chiCycKTwo (K := K))) :
    MpcChiKerLevel α r (fieldUni_nuPullbackM B e) := by
  intro z hz
  have h : chiCycKTwo (K := K) (e.1 z) = chiM α 0 z := e.2 z
  obtain ⟨y, hy⟩ := mpcCert_nu_le_of_chiKerTwo B (h.trans hz)
  exact ⟨y, by rw [← hr]; exact hy⟩

/-- **The level-`r` clause forces the level**, whenever `2^r` is the actual pivot value: `C̄₀`
lies in `ker χ_M`, so `nu_ker_chi_le` puts its transported value in `2^{B.r} ℤ₂`, and a value of
valuation exactly `r` cannot be more divisible than that.  Stated as the `r = 1` case, the only
one the frozen table uses: the pivot clause **implies** `B.r ≤ 1`. -/
theorem mpcCert_level_le_of_pivot (B : MarkedRecip Rec K) {α : ℕ}
    (e : OrientedContinuousMulEquiv (chiM α 0) (chiCycKTwo (K := K)))
    (hpivot : ∃ γ : ℤ_[2]ˣ, toAdd (fieldUni_nuPullbackM B e (dmC α 0)) = (γ : ℤ_[2]) * 2 ^ 1) :
    B.r ≤ 1 := by
  by_contra hlt
  obtain ⟨γ, hγ⟩ := hpivot
  have h : chiCycKTwo (K := K) (e.1 (dmC α 0)) = 1 := (e.2 _).trans (chiM_dmC α 0)
  obtain ⟨y, hy⟩ := mpcCert_nu_le_of_chiKerTwo B h
  have hval : (γ : ℤ_[2]) * 2 ^ 1 = 2 ^ B.r * y := hγ.symm.trans hy
  obtain ⟨j, hj⟩ : ∃ j, B.r = j + 2 := ⟨B.r - 2, by omega⟩
  have hcancel : (γ : ℤ_[2]) = 2 * (2 ^ j * y) := by
    have h2 : (2 : ℤ_[2]) * (γ : ℤ_[2]) = 2 * (2 * (2 ^ j * y)) := by
      rw [hj] at hval
      calc (2 : ℤ_[2]) * (γ : ℤ_[2]) = (γ : ℤ_[2]) * 2 ^ 1 := by ring
        _ = 2 ^ (j + 2) * y := hval
        _ = 2 * (2 * (2 ^ j * y)) := by ring
    exact mul_left_cancel₀ (by norm_num) h2
  have := γ.isUnit
  rw [hcancel] at this
  have hz : PadicInt.toZMod (2 * (2 ^ j * y) : ℤ_[2]) = 0 := by
    rw [map_mul, map_ofNat, show ((2 : ZMod 2)) = 0 from by decide, zero_mul]
  exact not_isUnit_zero (hz ▸ this.map (PadicInt.toZMod (p := 2)))

variable [CompactSpace AbsGalQ2] [TotallyDisconnectedSpace AbsGalQ2] {R : LocalReciprocity}

/-- **`ℚ₂(√10)`'s remaining input**, at wave 77's chosen oriented equivalence: the level is `1`
and the marked data sits at `(r, p) = (1, 0)`.  The tree carries none of this: wave 78 §2.3's
two arguments for `B.r = 1` are hand computations, and the `C̄₀`/`D̄`/`B̄` residues are separate
invariants of the χ-preserving action. -/
def MpcRowData_sqrtTen [T2Space (GalK KSqrtTen)] (B : MarkedRecip R KSqrtTen) : Prop :=
  B.r = 1 ∧ MpcMarkedData 2 1 (p false 1)
    (fieldUni_nuPullbackM B (fieldId_chosenEquivM_sqrtTen B))

/-- **`ℚ₂(√−10)`'s remaining input**, at `(r, p) = (1, 1)`: the `ε = true` row. -/
def MpcRowData_sqrtNegTen [T2Space (GalK KSqrtNegTen)] (B : MarkedRecip R KSqrtNegTen) : Prop :=
  B.r = 1 ∧ MpcMarkedData 2 1 (p true 1)
    (fieldUni_nuPullbackM B (fieldId_chosenEquivM_sqrtNegTen B))

/-- **THE `sqrtTen` ROW'S BRANCH DATUM**, on the row `Main.lean` actually assigns it.  Over the
field's own reciprocity bundle, the standing instance binders, and `MpcRowData_sqrtTen`. -/
theorem mpcCert_genAsmBranch_sqrtTen [T2Space (GalK KSqrtTen)] (B : MarkedRecip R KSqrtTen)
    (hrow : MpcRowData_sqrtTen B) :
    ∃ G : GenAsmBranch KSqrtTen B, G.pres = .Mpc 2 1 false .one 0 :=
  mpcCert_genAsmBranch_of_orientedMpc 1 (p false 1) false .one (le_refl 2) (by omega)
    (by rw [finrank_KSqrtTen]; rfl) (fieldId_chosenEquivM_sqrtTen B)
    (mpcCert_chiKerLevel_of_level B hrow.1 _) hrow.2

/-- **THE `sqrtNegTen` ROW'S BRANCH DATUM**, on the row `Main.lean` actually assigns it. -/
theorem mpcCert_genAsmBranch_sqrtNegTen [T2Space (GalK KSqrtNegTen)]
    (B : MarkedRecip R KSqrtNegTen) (hrow : MpcRowData_sqrtNegTen B) :
    ∃ G : GenAsmBranch KSqrtNegTen B, G.pres = .Mpc 2 1 true .one 0 :=
  mpcCert_genAsmBranch_of_orientedMpc 1 (p true 1) true .one (le_refl 2) (by omega)
    (by rw [finrank_KSqrtNegTen]; rfl) (fieldId_chosenEquivM_sqrtNegTen B)
    (mpcCert_chiKerLevel_of_level B hrow.1 _) hrow.2

end Fields

/-! ## §7 Axiom pins

One pin per declaration, in declaration order.  Three sets occur, all already committed; this
lane introduces no axiom of its own.

* **The standard three** (`propext, Classical.choice, Quot.sound`) on everything in §1, §2, §5's
  realization, and §6's transport lemmas.  In particular `mpcCert_shift_mem`, the invariance
  principle, and `mpcCert_level_le_of_pivot`, the necessity direction, cost no axiom: they are
  bundle arithmetic.
* **Plus `peripheralCyclotomicAction`** on `mpcCert_markedMatching` and everything downstream of
  it (both certificate producers, the branch-datum producer, the two field rows).  The single
  source is `MScaling.mScalingHypothesis_zero`, the M3 row.  This is the same axiom wave 78's
  `M`-row data carry, so the procyclic route adds nothing on that side.
* **Plus the even route's endpoint set** (`hilbertSymbol_normCriterion_finiteDyadic`,
  `tateDualityAt`, `Foundations.absGalQ2_isTopologicallyFinitelyGenerated`,
  `Foundations.absGalQ2_localEulerCharacteristic`) on `MpcRowData_sqrt{Ten,NegTen}` and the two
  field theorems, through `fieldId_chosenEquivM_sqrt{Ten,NegTen}`.  Note this set already
  appears in the *statements* of the two named `Prop`s, because the clause is asserted at wave
  77's chosen oriented equivalence.

So `mpcCert_genAsmBranch_sqrt{Ten,NegTen}` sit at **exactly** the axiom set of wave 77's
`fieldId_genAsmBranch_sqrt{Ten,NegTen}`: moving the two fields off the vacuous `M0` row and onto
the `Mpc` row they belong on costs no axiom. -/

section AxiomPins

#print axioms mpcCert_nuMpc
#print axioms mpcCert_ztwoIota_mpcNu
#print axioms mpcCert_toAdd_ztwoIota_zpow
#print axioms mpcCert_toAdd_nuMpc_gen
#print axioms mpcCert_toAdd_nuMpc_dmA
#print axioms mpcCert_toAdd_nuMpc_dmB
#print axioms mpcCert_toAdd_nuMpc_dmC
#print axioms mpcCert_toAdd_nuMpc_dmD
#print axioms MpcChiKerLevel
#print axioms MpcMarkedData
#print axioms mpcCert_shift_mem
#print axioms mpcCert_dmD_shift
#print axioms mpcCert_dmB_shift
#print axioms mpcCert_markedMatching
#print axioms mpcCert_transport
#print axioms MarkedCoreCertificateMpc
#print axioms mpcCert_marked_matching_certificate_Mpc
#print axioms MarkedCoreCertificateKTwoMpc
#print axioms mpcCert_marked_matching_certificate_KTwoMpc
#print axioms mpcCert_realization
#print axioms mpcCert_genAsmBranch_of_orientedMpc
#print axioms mpcCert_nu_le_of_chiKerTwo
#print axioms mpcCert_chiKerLevel_of_level
#print axioms mpcCert_level_le_of_pivot
#print axioms MpcRowData_sqrtTen
#print axioms MpcRowData_sqrtNegTen
#print axioms mpcCert_genAsmBranch_sqrtTen
#print axioms mpcCert_genAsmBranch_sqrtNegTen

end AxiomPins

end

end GQ2.Dyadic.Instances.MpcCert
