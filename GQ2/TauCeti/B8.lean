/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Fable 5.1
-/
module

public import TauCeti.Topology.Algebra.Group.Profinite.Free.Peripheral.Dyadic
public import GQ2.TauCeti.ProPDict

@[expose] public section

/-!
# B8 from Tau Ceti: the peripheral cyclotomic action

Ticket B8 of the Tau Ceti discharge campaign (`docs/orchestration/tauceti-tickets.md`).  This
module builds `peripheralCyclotomicAction_tauceti`, a term of `GQ2.PeripheralCyclotomicAction`
whose type is that of the `peripheralCyclotomicAction` field of `GQ2.LiteratureInputs`, from Tau
Ceti's dyadic peripheral theorem `TauCeti.Peripheral.exists_peripheralPowerAutomorphism_two`:
for a marked free pro-`2` group `e : F ≃ₜ* freeProP 2 (Fin 2)` and `u ∈ ℤ₂ˣ`, a continuous
automorphism carrying the peripheral elements `P, T, C = (PT)⁻¹` to conjugates of their `u`-th
`2`-adic powers, with the conjugator of `P` normalized to `1`.

The bridge has three parts, all through the P1 dictionary (`GQ2/TauCeti/ProPDict.lean`).

* **The cyclotomic exponent `ι : ℤ₂ˣ → ℤ̂`** (`peripheralIota`).  gq2 pins `ι` by `ι 1 = ω₂` and
  `zhatProjTwo (ι u) = u`.  The plan's "`u` at `2`, trivial odd part" is not provable (gq2 never
  shows that the odd components of `ω₂` vanish; memo correction B8), so instead
  `ι u := zhatEquiv⁻¹ (ω₂ · s u)` where `s u := zhatSectionTwo (u - 1) + 1` is the profinite
  integer with `2`-adic component `u` and odd components `1` (`zhatShiftedSectionTwo`).  Then
  `ι 1 = ω₂` since `s 1 = 1`, and the `2`-adic component of `ι u` is
  `component 2 ω₂ · u = u` by P1's `component_two_zhatEquiv_omega2`.
* **The generators** (`periphP_deltaEquiv`, `periphT_deltaEquiv`, `periphC_deltaEquiv`): under
  P1's `deltaEquiv : Δ ≃ₜ* freeProP 2 (Fin 2)`, Tau Ceti's `periphP/T/C deltaEquiv` are gq2's
  `deltaP/T/C`.  Tau Ceti's conjugation `c⁻¹ * x * c` is gq2's `conjP x c` by `rfl`.
* **The powers** (`zpowHat_peripheralIota`): on `Δ`, gq2's `x ^ᶻ ι u` is Tau Ceti's
  `padicPow x u`, by P1's `zpowHat_eq_padicPow` and the component computation.

The existence statement is first restated on gq2's data (`exists_peripheralAut`), rewriting the
`periph*` terms *before* choosing (rewriting inside `.choose` fails: the motive is not type
correct); the bundle then takes `aut u`, `cT u`, `cC u` by `Classical.choose` and `cP u := 1`.
-/

open Multiplicative

namespace GQ2.TauCetiBridge

/-! ## The cyclotomic exponent `ι : ℤ₂ˣ → ℤ̂` -/

/-- `v ↦ (v at 2, 1 at every odd prime)`: the profinite integer `zhatSectionTwo (v - 1) + 1`,
with `2`-adic component `v` (`component_two_zhatShiftedSectionTwo`) and value `1` at `v = 1`
(`zhatShiftedSectionTwo_one`).  Multiplying `ω₂` by it leaves the odd components of `ω₂`
untouched, which is what makes `ι 1 = ω₂` provable. -/
noncomputable def zhatShiftedSectionTwo (v : ℤ_[2]) : Additive TauCeti.zHat.{0} :=
  zhatSectionTwo (v - 1) + 1

@[simp]
theorem component_two_zhatShiftedSectionTwo (v : ℤ_[2]) :
    TauCeti.zHat.component 2 (zhatShiftedSectionTwo v) = v := by
  rw [zhatShiftedSectionTwo, map_add, map_one, component_two_zhatSectionTwo, sub_add_cancel]

@[simp]
theorem zhatShiftedSectionTwo_one : zhatShiftedSectionTwo 1 = 1 := by
  rw [zhatShiftedSectionTwo, sub_self, zhatSectionTwo_zero, zero_add]

theorem continuous_zhatShiftedSectionTwo : Continuous zhatShiftedSectionTwo := by
  unfold zhatShiftedSectionTwo
  exact (continuous_zhatSectionTwo.comp (continuous_id.sub continuous_const)).add continuous_const

/-- **The cyclotomic exponent** `ι u := zhatEquiv⁻¹ (ω₂ · (u at 2, 1 at odd primes))`, the `ι`
field of `peripheralCyclotomicAction_tauceti`.  Its `2`-adic component is `u`
(`zhatProjTwo_peripheralIota`) and `ι 1 = ω₂` (`peripheralIota_one`); the product is the ring
product of `Additive TauCeti.zHat`. -/
noncomputable def peripheralIota (u : ℤ_[2]ˣ) : GQ2.Zhat :=
  zhatEquiv.symm (Additive.toMul
    (Additive.ofMul (zhatEquiv GQ2.omega2) * zhatShiftedSectionTwo (u : ℤ_[2])))

/-- `ι 1 = ω₂` (the `hι_one` field). -/
@[simp]
theorem peripheralIota_one : peripheralIota 1 = GQ2.omega2 := by
  rw [peripheralIota, Units.val_one, zhatShiftedSectionTwo_one, mul_one, toMul_ofMul,
    ContinuousMulEquiv.symm_apply_apply]

/-- The `2`-adic component of (the Tau Ceti image of) `ι u` is `u`. -/
@[simp]
theorem component_two_zhatEquiv_peripheralIota (u : ℤ_[2]ˣ) :
    TauCeti.zHat.component 2 (Additive.ofMul (zhatEquiv (peripheralIota u))) = u := by
  rw [peripheralIota, ContinuousMulEquiv.apply_symm_apply, ofMul_toMul, map_mul,
    component_two_zhatEquiv_omega2, component_two_zhatShiftedSectionTwo, one_mul]

/-- `zhatProjTwo (ι u) = u` (the `hι_proj` field). -/
@[simp]
theorem zhatProjTwo_peripheralIota (u : ℤ_[2]ˣ) :
    GQ2.zhatProjTwo (peripheralIota u) = ofAdd (u : ℤ_[2]) := by
  rw [zhatProjTwo_eq_component, component_two_zhatEquiv_peripheralIota]

/-- `ι` is continuous (the `hι_cont` field). -/
theorem continuous_peripheralIota : Continuous peripheralIota := by
  unfold peripheralIota
  exact zhatEquiv.symm.continuous.comp (continuous_toMul.comp (continuous_const.mul
    (continuous_zhatShiftedSectionTwo.comp Units.continuous_val)))

/-- On `Δ`, gq2's `x ^ᶻ ι u` is Tau Ceti's `u`-th `2`-adic power `padicPow x u`. -/
theorem zpowHat_peripheralIota (x : GQ2.Delta) (u : ℤ_[2]ˣ) :
    x ^ᶻ peripheralIota u = isProP_tauCeti_delta.padicPow x (u : ℤ_[2]) := by
  rw [zpowHat_eq_padicPow GQ2.isProP_maxProPQuotient x, component_two_zhatEquiv_peripheralIota]

/-! ## The peripheral generators of `Δ` under `deltaEquiv` -/

/-- Tau Ceti's first peripheral element of the marked group `deltaEquiv` is gq2's `P`. -/
@[simp]
theorem periphP_deltaEquiv : TauCeti.Peripheral.periphP deltaEquiv = GQ2.deltaP := by
  rw [TauCeti.Peripheral.periphP_eq_basis, TauCeti.Peripheral.basis_apply, deltaEquiv_symm_of_zero]

/-- Tau Ceti's second peripheral element of the marked group `deltaEquiv` is gq2's `T`. -/
@[simp]
theorem periphT_deltaEquiv : TauCeti.Peripheral.periphT deltaEquiv = GQ2.deltaT := by
  rw [TauCeti.Peripheral.periphT_eq_basis, TauCeti.Peripheral.basis_apply, deltaEquiv_symm_of_one]

/-- Tau Ceti's third peripheral element `(PT)⁻¹` of the marked group `deltaEquiv` is gq2's `C`. -/
@[simp]
theorem periphC_deltaEquiv : TauCeti.Peripheral.periphC deltaEquiv = GQ2.deltaC := by
  rw [TauCeti.Peripheral.periphC_def, periphP_deltaEquiv, periphT_deltaEquiv]
  rfl

/-! ## The automorphisms -/

/-- **Tau Ceti's dyadic peripheral theorem on gq2's `Δ`**: for every `u ∈ ℤ₂ˣ` there is a
continuous automorphism `φ` of `Δ` with `φ P = P ^ᶻ ι u`, `φ T = conjP (T ^ᶻ ι u) cT` and
`φ C = conjP (C ^ᶻ ι u) cC` (gq2's conjugation `conjP x c = c⁻¹ x c`), the conjugator of `P`
being `1`.  This is `TauCeti.Peripheral.exists_peripheralPowerAutomorphism_two` at
`e = deltaEquiv`, with the peripheral elements and the `2`-adic powers rewritten to gq2's. -/
theorem exists_peripheralAut (u : ℤ_[2]ˣ) :
    ∃ (φ : ContinuousMulEquiv GQ2.Delta GQ2.Delta) (cP cT cC : GQ2.Delta), cP = 1 ∧
      φ GQ2.deltaP = GQ2.conjP (GQ2.deltaP ^ᶻ peripheralIota u) cP ∧
      φ GQ2.deltaT = GQ2.conjP (GQ2.deltaT ^ᶻ peripheralIota u) cT ∧
      φ GQ2.deltaC = GQ2.conjP (GQ2.deltaC ^ᶻ peripheralIota u) cC := by
  obtain ⟨φ, cP, cT, cC, hcP, hP, hT, hC⟩ :=
    TauCeti.Peripheral.exists_peripheralPowerAutomorphism_two isProP_tauCeti_delta deltaEquiv u
  rw [periphP_deltaEquiv] at hP
  rw [periphT_deltaEquiv] at hT
  rw [periphC_deltaEquiv] at hC
  exact ⟨φ, cP, cT, cC, hcP, by rw [hP, zpowHat_peripheralIota]; rfl,
    by rw [hT, zpowHat_peripheralIota]; rfl, by rw [hC, zpowHat_peripheralIota]; rfl⟩

/-- **B8 from Tau Ceti: the peripheral cyclotomic action** (gq2's Lemma 3.6 bundle).  `ι` is
`peripheralIota`; for each `u`, `aut u`, `cT u`, `cC u` are chosen from `exists_peripheralAut u`,
and `cP u = 1`. -/
noncomputable def peripheralCyclotomicAction_tauceti : GQ2.PeripheralCyclotomicAction where
  ι := peripheralIota
  hι_cont := continuous_peripheralIota
  hι_one := peripheralIota_one
  hι_proj := zhatProjTwo_peripheralIota
  aut u := (exists_peripheralAut u).choose
  cP _ := 1
  cT u := (exists_peripheralAut u).choose_spec.choose_spec.choose
  cC u := (exists_peripheralAut u).choose_spec.choose_spec.choose_spec.choose
  hP u :=
    -- `rw [← hcP]` would also hit the `1` of the `cP = 1` conjunct under `.choose`; compose.
    (exists_peripheralAut u).choose_spec.choose_spec.choose_spec.choose_spec.2.1.trans
      (congrArg (GQ2.conjP _)
        (exists_peripheralAut u).choose_spec.choose_spec.choose_spec.choose_spec.1)
  hT u := (exists_peripheralAut u).choose_spec.choose_spec.choose_spec.choose_spec.2.2.1
  hC u := (exists_peripheralAut u).choose_spec.choose_spec.choose_spec.choose_spec.2.2.2

@[simp]
theorem peripheralCyclotomicAction_tauceti_ι :
    peripheralCyclotomicAction_tauceti.ι = peripheralIota :=
  rfl

@[simp]
theorem peripheralCyclotomicAction_tauceti_cP (u : ℤ_[2]ˣ) :
    peripheralCyclotomicAction_tauceti.cP u = 1 :=
  rfl

end GQ2.TauCetiBridge
