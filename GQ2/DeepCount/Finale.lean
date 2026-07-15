/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Opus-4.8 and Fable-5
-/
module

public import GQ2.DeepCount.Transport

@[expose] public section

/-!
# The structural deep-count theorem

The final assembly of the arithmetic, filtration, and duality inputs.

See `GQ2.DeepCount` for the paper-facing overview, source citations, and deviations.
-/

namespace GQ2

open ContCoh LocalKummer

local notation "ℚ̄₂" => AlgebraicClosure ℚ_[2]

/-! ## The finale: `hduality`

The instantiation of the abstract engine `card_equivHoms_deep_eq_quot` at
`M := H¹(ker ρ, 𝔽₂)` (`conjModule`), `U := V^∨` (`dualModule`),
`Deep := deepClassesSubgroup`, `E := midClassesSubgroup`, `B := pairingK` — every input a
named, verified producer; the conclusion is EXACTLY the `hduality` hypothesis of the f6
capstone `card_deepPart_sq_of_duality` (and hence of f8's `lemma_6_17_dim_of_hduality`). -/

section Finale

variable {C : Type} [Group C] [TopologicalSpace C] [Finite C]
variable {V : Type} [AddCommGroup V] [DistribMulAction C V] [Finite V]
variable (ρ : ContinuousMonoidHom AbsGalQ2 C)

/-- **`hduality`** — the deep-part proof's result.  Inputs: the `V^∨` regular-summand package
(f8's Lemma-6.11 output at `dualModule`: `hsimple`/`hnt`/`ι`/`r`/`hι`/`hr`/`hri`), the
self-duality `eU`/`heU` (§H's `dualSelfDual(_equivariant)` given the 6.17 invariant form),
the dualized inertia `ht₀U` (§H's `exists_dualModule_smul_ne` given `hram`), a
residue-trivial lift `g₀` of `t₀` (tame inertia; the f8 arithmetic), and the B13 bundle
data for the splitting field `k` with the pointwise kernel identification `hker`. -/
theorem hduality_of_data (hρsurj : Function.Surjective ⇑ρ)
    [Finite (H1 ↥(ρ.toMonoidHom.ker : Subgroup AbsGalQ2) (ZMod 2))]
    (hsimple : ∀ S : AddSubgroup (V →+ ZMod 2),
      (∀ (h : C), ∀ w ∈ S,
        (dualModule : DistribMulAction C (V →+ ZMod 2)).toSMul.smul h w ∈ S) →
      S = ⊥ ∨ S = ⊤)
    (hnt : Nontrivial (V →+ ZMod 2))
    {Nreg : ℕ} (ι : (V →+ ZMod 2) →+ (Fin Nreg → C → ZMod 2))
    (r : (Fin Nreg → C → ZMod 2) →+ (V →+ ZMod 2))
    (hι : ∀ (h : C) (φ : V →+ ZMod 2) (n : Fin Nreg) (x : C),
      ι ((dualModule : DistribMulAction C (V →+ ZMod 2)).toSMul.smul h φ) n x
        = ι φ n (h⁻¹ * x))
    (hr : ∀ (h : C) (F : Fin Nreg → C → ZMod 2),
      r (fun n x => F n (h⁻¹ * x))
        = (dualModule : DistribMulAction C (V →+ ZMod 2)).toSMul.smul h (r F))
    (hri : ∀ φ : V →+ ZMod 2, r (ι φ) = φ)
    (eU : (V →+ ZMod 2) ≃+ ((V →+ ZMod 2) →+ ZMod 2))
    (heU : ∀ (c : C) (φ : V →+ ZMod 2),
      letI : DistribMulAction C (V →+ ZMod 2) := dualModule
      eU ((dualModule : DistribMulAction C (V →+ ZMod 2)).toSMul.smul c φ)
        = (dualModule : DistribMulAction C ((V →+ ZMod 2) →+ ZMod 2)).toSMul.smul c (eU φ))
    (t₀ : C)
    (ht₀U : ∃ φ : V →+ ZMod 2,
      (dualModule : DistribMulAction C (V →+ ZMod 2)).toSMul.smul t₀ φ ≠ φ)
    (g₀ : AbsGalQ2) (hg₀ : ρ g₀ = t₀)
    (hg₀rt : IsResidueTrivial (ρ.toMonoidHom.ker : Subgroup AbsGalQ2) g₀)
    (k : IntermediateField ℚ_[2] ℚ̄₂) [FiniteDimensional ℚ_[2] k]
    (htriv : ∀ (g : k.fixingSubgroup) (m : ZMod 2), g • m = m)
    (hker : ∀ x : Kummer.GaloisGroup ℚ_[2],
      x ∈ (ρ.toMonoidHom.ker : Subgroup AbsGalQ2) ↔ x ∈ k.fixingSubgroup)
    (π : ℚ̄₂) (hπk : π ∈ k) (hπ0 : π ≠ 0) (hπ1 : ‖π‖ < 1)
    (hπmax : ∀ x : ℚ̄₂, x ∈ k → ‖x‖ < 1 → ‖x‖ ≤ ‖π‖)
    {e : ℕ} (he : ‖(2 : ℚ̄₂)‖ = ‖π‖ ^ e) (he_pos : 1 ≤ e) {f : ℕ} (hf_pos : 1 ≤ f)
    (hcard_zero : Nat.card (↥(normUnits k) ⧸
      (depthUnits k π 1).subgroupOf (normUnits k)) = 2 ^ f - 1)
    (hcard_gr : ∀ i : ℕ, 1 ≤ i → Nat.card (↥(depthUnits k π i) ⧸
      (depthUnits k π (i + 1)).subgroupOf (depthUnits k π i)) = 2 ^ f) :
    letI := conjModuleDeep ρ hρsurj
    letI := conjModuleQuot ρ hρsurj
    letI : DistribMulAction C (V →+ ZMod 2) := dualModule
    Nat.card ↥(equivHoms C (V →+ ZMod 2)
        ↥(deepClassesSubgroup (ρ.toMonoidHom.ker : Subgroup AbsGalQ2)))
      = Nat.card ↥(equivHoms C (V →+ ZMod 2)
          (H1 ↥(ρ.toMonoidHom.ker : Subgroup AbsGalQ2) (ZMod 2) ⧸
            deepClassesSubgroup (ρ.toMonoidHom.ker : Subgroup AbsGalQ2))) := by
  letI := conjModule ρ hρsurj
  letI instDeepI := conjModuleDeep ρ hρsurj
  letI instQI := conjModuleQuot ρ hρsurj
  letI : DistribMulAction C (V →+ ZMod 2) := dualModule
  haveI : Finite (V →+ ZMod 2) :=
    Finite.of_injective (DFunLike.coe : (V →+ ZMod 2) → (V → ZMod 2)) DFunLike.coe_injective
  have h2M : ∀ m : H1 ↥(ρ.toMonoidHom.ker : Subgroup AbsGalQ2) (ZMod 2), m + m = 0 :=
    fun m => h1_add_self m
  have h2U : ∀ φ : V →+ ZMod 2, φ + φ = 0 := fun φ => FoxH.ElemDual.add_self_eq_zero φ
  have hsharp : pairPerp (pairingK ρ)
        (deepClassesSubgroup (ρ.toMonoidHom.ker : Subgroup AbsGalQ2))
      ≤ midClassesSubgroup (ρ.toMonoidHom.ker : Subgroup AbsGalQ2) :=
    pairPerp_le_of_card_le (pairingK ρ) h2M (pairingK_nondeg ρ)
      (midClassesSubgroup_le_pairPerp_pairingK ρ k htriv hker)
      (card_quot_deep_le_card_mid_ker ρ k hker π hπk hπ0 hπ1 hπmax he he_pos hf_pos
        hcard_zero hcard_gr)
  exact card_equivHoms_deep_eq_quot (C := C) h2M h2U hsimple hnt ι r hι hr hri eU heU t₀
    ht₀U (pairingK ρ) (fun c x y => pairingK_conjModule ρ hρsurj c x y) (pairingK_nondeg ρ)
    (deepClassesSubgroup (ρ.toMonoidHom.ker : Subgroup AbsGalQ2))
    (midClassesSubgroup (ρ.toMonoidHom.ker : Subgroup AbsGalQ2))
    (fun c x hx => conjAct_deepClasses ρ (Function.surjInv hρsurj c) hx)
    (deepClassesSubgroup_le_pairPerp_pairingK ρ k htriv hker)
    hsharp
    (fun d x hx => conjAct_surjInv_conj_mid_sub_mem_deep ρ hρsurj hg₀ hg₀rt d hx)
    (instDeep := instDeepI)
    (fun c x => rfl)
    (instQ := instQI)
    (fun c m => (conjActQuotHom_mk ρ (Function.surjInv hρsurj c) m).symm)

end Finale

end GQ2
