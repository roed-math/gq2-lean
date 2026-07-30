/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Opus-4.8 and Fable-5
-/
module

public import GQ2.Dyadic.MarkedCore.HandleMixClear

@[expose] public section

/-!
# Handle mixing, step 5: the χ-side, and the packaged per-family headline

**Ticket HM5** of the dyadic campaign (lane MC) — the closing ticket of the `HandleMixLift`
discharge.
-/

open Multiplicative

namespace GQ2

namespace Dyadic

namespace MarkedCore

/-! ## §1 Precomposition stabilizers -/

section EndStabilizer

/-- **The precomposition stabilizer of `g`**, as a submonoid of `Function.End X`: the self-maps
of `X` that `g` cannot see.  `Function.End`'s product is `E₁ * E₂ = E₁ ∘ E₂`, so closure under
multiplication is one composition of the two hypotheses. -/
def endStabilizer {X Y : Type*} (g : X → Y) : Submonoid (Function.End X) where
  carrier := {E | ∀ x, g (E x) = g x}
  mul_mem' {_E₁ E₂} h₁ h₂ x := (h₁ (E₂ x)).trans (h₂ x)
  one_mem' _ := rfl

@[simp] theorem mem_endStabilizer {X Y : Type*} (g : X → Y) (E : Function.End X) :
    E ∈ endStabilizer g ↔ ∀ x, g (E x) = g x := Iff.rfl

/-- **Generator-wise blindness suffices**: if `g` does not see any generator of `S`, it does not
see any element of `Submonoid.closure S`. -/
theorem closure_le_endStabilizer {X Y : Type*} (g : X → Y) {S : Set (Function.End X)}
    (hS : ∀ E ∈ S, ∀ x, g (E x) = g x) : Submonoid.closure S ≤ endStabilizer g :=
  Submonoid.closure_le.mpr hS

end EndStabilizer

/-! ## §2 An automorphism read as a continuous endomorphism -/

section AutHom

/-- A continuous automorphism read as a continuous endomorphism — the `⟨Ψ.toMonoidHom, …⟩` idiom
of HM4 §4, named once. -/
def autHom {X : Type} [Group X] [TopologicalSpace X] (Ψ : ContinuousMulEquiv X X) :
    ContinuousMonoidHom X X := ⟨Ψ.toMonoidHom, Ψ.continuous_toFun⟩

@[simp] theorem autHom_apply {X : Type} [Group X] [TopologicalSpace X]
    (Ψ : ContinuousMulEquiv X X) (x : X) : autHom Ψ x = Ψ x := rfl

variable {A : Type} [Group A] [TopologicalSpace A] [IsTopologicalGroup A] [T2Space A] {α h : ℕ}

/-- **Generators decide invariance, on `D_M`**: a character fixed on the marked generators by `Ψ`
is fixed by `Ψ` everywhere (MC2's `dm_hom_ext`). -/
theorem dm_char_fixed (f : ContinuousMonoidHom (DM α h : Type) A)
    (Ψ : ContinuousMulEquiv (DM α h : Type) (DM α h : Type))
    (hgen : ∀ i, f (Ψ (dmGen α h i)) = f (dmGen α h i)) (x : (DM α h : Type)) :
    f (Ψ x) = f x :=
  DFunLike.congr_fun (dm_hom_ext (f.comp (autHom Ψ)) f hgen) x

/-- The `N`-mirror of `dm_char_fixed`. -/
theorem dn_char_fixed (f : ContinuousMonoidHom (DN α h : Type) A)
    (Ψ : ContinuousMulEquiv (DN α h : Type) (DN α h : Type))
    (hgen : ∀ i, f (Ψ (dnGen α h i)) = f (dnGen α h i)) (x : (DN α h : Type)) :
    f (Ψ x) = f x :=
  DFunLike.congr_fun (dn_hom_ext (f.comp (autHom Ψ)) f hgen) x

end AutHom

/-! ## §3 The exact χ-action of the four clearing generators -/

section ClearBlind

/-- **The χ-side condition on a frame row** — the exact hypothesis under which every generator of
`A(P,h)` is invisible to a character.  The clearing moves shift the `d̄`-slot and the handle slots
by the **pivot** value (the index-`2` slot: `c̄ = C̄₀` for `M`, `σ̄` for `N`) and by the partner
handle value; so a character trivial at the pivot and on the whole handle plane is fixed by all of
them.  Both standard orientations satisfy it on the nose (`isClearBlind_chiM`,
`isClearBlind_chiN`), and this is the exact χ-side companion of HM4's ν-side unit hypothesis: the
clearing steers `ν` because `ν(pivot)` is a **unit**, and fixes `χ` because `χ(pivot)` is
**trivial** — one slot, read additively and multiplicatively. -/
def IsClearBlind {A : Type*} [One A] {h : ℕ} (v : Fin (coreRank h) → A) : Prop :=
  v 2 = 1 ∧ (∀ j : Fin h, v (handleIdxU j) = 1) ∧ ∀ j : Fin h, v (handleIdxV j) = 1

variable {A : Type} [CommGroup A] [TopologicalSpace A] (α h : ℕ)

/-! ### The untouched slots

Each `τ` family moves exactly one slot and `Φ_j` exactly two, so all but those slots are fixed by
*any* character — no hypothesis, no pro-2 structure on the target. -/

theorem char_dmTauU_of_ne (f : ContinuousMonoidHom (DM α h : Type) A) (j : Fin h) (k : ℤ_[2])
    {i : Fin (coreRank h)} (hi : i ≠ handleIdxU j) :
    f (dmTauUEquiv α h j k (dmGen α h i)) = f (dmGen α h i) := by
  rw [dmTauUEquiv_gen, tauUMark_of_ne _ _ _ _ hi]

theorem char_dmTauV_of_ne (f : ContinuousMonoidHom (DM α h : Type) A) (j : Fin h) (k : ℤ_[2])
    {i : Fin (coreRank h)} (hi : i ≠ handleIdxV j) :
    f (dmTauVEquiv α h j k (dmGen α h i)) = f (dmGen α h i) := by
  rw [dmTauVEquiv_gen, tauVMark_of_ne _ _ _ _ hi]

theorem char_dmTauD_of_ne (f : ContinuousMonoidHom (DM α h : Type) A) (k : ℤ_[2])
    {i : Fin (coreRank h)} (hi : i ≠ 3) :
    f (dmTauDEquiv α h k (dmGen α h i)) = f (dmGen α h i) := by
  rw [dmTauDEquiv_gen, tauDMark_of_ne _ _ _ hi]

theorem char_dnTauU_of_ne (f : ContinuousMonoidHom (DN α h : Type) A) (j : Fin h) (k : ℤ_[2])
    {i : Fin (coreRank h)} (hi : i ≠ handleIdxU j) :
    f (dnTauUEquiv α h j k (dnGen α h i)) = f (dnGen α h i) := by
  rw [dnTauUEquiv_gen, tauUMark_of_ne _ _ _ _ hi]

theorem char_dnTauV_of_ne (f : ContinuousMonoidHom (DN α h : Type) A) (j : Fin h) (k : ℤ_[2])
    {i : Fin (coreRank h)} (hi : i ≠ handleIdxV j) :
    f (dnTauVEquiv α h j k (dnGen α h i)) = f (dnGen α h i) := by
  rw [dnTauVEquiv_gen, tauVMark_of_ne _ _ _ _ hi]

theorem char_dnTauD_of_ne (f : ContinuousMonoidHom (DN α h : Type) A) (k : ℤ_[2])
    {i : Fin (coreRank h)} (hi : i ≠ 3) :
    f (dnTauDEquiv α h k (dnGen α h i)) = f (dnGen α h i) := by
  rw [dnTauDEquiv_gen, tauDMark_of_ne _ _ _ hi]

/-! ### The moved slots

The `τ`-rows need `map_zpowZtwo`, hence a pro-2 target; `Φ_j`'s two rows are HM3's
`frame_dmMixEquiv_dmD`/`_handleU` and `frame_dnMixEquiv_dnX2`/`_handleU`, already stated for an
arbitrary character into a commutative group, and are not restated here. -/

section MovedSlots

variable [IsTopologicalGroup A] [CompactSpace A] [T2Space A] [TotallyDisconnectedSpace A]
  (hA : IsProP 2 A)

/-- **The moved slot of `τ_{v_j}(k)`, through a character**: `ū_j ↦ v̄_j^k · ū_j`. -/
theorem char_dmTauU_handleU (f : ContinuousMonoidHom (DM α h : Type) A) (j : Fin h) (k : ℤ_[2]) :
    f (dmTauUEquiv α h j k (dmGen α h (handleIdxU j)))
      = zpowZtwo hA (f (dmGen α h (handleIdxV j))) k * f (dmGen α h (handleIdxU j)) := by
  rw [dmTauUEquiv_gen, map_tauUMark (isProP_DM α h) hA f, tauUMark_handleU_self]

/-- **The moved slot of `τ_{u_j}(k)`**: `v̄_j ↦ ū_j^k · v̄_j`. -/
theorem char_dmTauV_handleV (f : ContinuousMonoidHom (DM α h : Type) A) (j : Fin h) (k : ℤ_[2]) :
    f (dmTauVEquiv α h j k (dmGen α h (handleIdxV j)))
      = zpowZtwo hA (f (dmGen α h (handleIdxU j))) k * f (dmGen α h (handleIdxV j)) := by
  rw [dmTauVEquiv_gen, map_tauVMark (isProP_DM α h) hA f, tauVMark_handleV_self]

/-- **The moved slot of `τ_c(k)`**: `d̄ ↦ c̄^k · d̄` — the one row where the *pivot* enters a core
letter. -/
theorem char_dmTauD_three (f : ContinuousMonoidHom (DM α h : Type) A) (k : ℤ_[2]) :
    f (dmTauDEquiv α h k (dmD α h)) = zpowZtwo hA (f (dmC α h)) k * f (dmD α h) := by
  rw [dmC, dmD, dmTauDEquiv_gen, map_tauDMark (isProP_DM α h) hA f, tauDMark_three]

/-! ### `D_N`

Same four rows; for `N` the pivot letter at index `2` is `σ` itself. -/

theorem char_dnTauU_handleU (f : ContinuousMonoidHom (DN α h : Type) A) (j : Fin h) (k : ℤ_[2]) :
    f (dnTauUEquiv α h j k (dnGen α h (handleIdxU j)))
      = zpowZtwo hA (f (dnGen α h (handleIdxV j))) k * f (dnGen α h (handleIdxU j)) := by
  rw [dnTauUEquiv_gen, map_tauUMark (isProP_DN α h) hA f, tauUMark_handleU_self]

theorem char_dnTauV_handleV (f : ContinuousMonoidHom (DN α h : Type) A) (j : Fin h) (k : ℤ_[2]) :
    f (dnTauVEquiv α h j k (dnGen α h (handleIdxV j)))
      = zpowZtwo hA (f (dnGen α h (handleIdxU j))) k * f (dnGen α h (handleIdxV j)) := by
  rw [dnTauVEquiv_gen, map_tauVMark (isProP_DN α h) hA f, tauVMark_handleV_self]

/-- **The moved slot of `τ_σ(k)` on `D_N`**: `x̄₂ ↦ σ̄^k · x̄₂`. -/
theorem char_dnTauD_three (f : ContinuousMonoidHom (DN α h : Type) A) (k : ℤ_[2]) :
    f (dnTauDEquiv α h k (dnX2 α h)) = zpowZtwo hA (f (dnSigma α h)) k * f (dnX2 α h) := by
  rw [dnSigma, dnX2, dnTauDEquiv_gen, map_tauDMark (isProP_DN α h) hA f, tauDMark_three]

/-! ### The `Φ_j` rows, in blind form

HM3 states `Φ_j`'s two moved rows for an arbitrary character (`frame_dmMixEquiv_dmD`,
`frame_dmMixEquiv_handleU`, and the `N`-mirrors): both pick up the **same** factor
`f(c̄)·f(v̄_j)⁻¹`.  So `Φ_j` is invisible to `f` exactly when that factor is `1` — which is what
`IsClearBlind` gives, and which a general character need **not** satisfy. -/

/-! ### Every generator of `A(P,h)` is invisible to a clear-blind character

The pattern is the same eight times: `dm_char_fixed`/`dn_char_fixed` reduce to the marked
generators, one `by_cases` isolates the moved slot, and the blindness rows kill the correction. -/

include hA in
/-- **`τ_{v_j}(k)` is invisible to a clear-blind character of `D_M`.** -/
theorem char_dmTauUEquiv_fixed (f : ContinuousMonoidHom (DM α h : Type) A)
    (hv : IsClearBlind fun i => f (dmGen α h i)) (j : Fin h) (k : ℤ_[2]) (x : (DM α h : Type)) :
    f (dmTauUEquiv α h j k x) = f x := by
  have hV : f (dmGen α h (handleIdxV j)) = 1 := hv.2.2 j
  refine dm_char_fixed f _ (fun i => ?_) x
  by_cases hi : i = handleIdxU j
  · subst hi
    rw [char_dmTauU_handleU α h hA f j k, hV, zpowZtwo_one_base, one_mul]
  · exact char_dmTauU_of_ne α h f j k hi

include hA in
/-- **`τ_{u_j}(k)` is invisible to a clear-blind character of `D_M`.** -/
theorem char_dmTauVEquiv_fixed (f : ContinuousMonoidHom (DM α h : Type) A)
    (hv : IsClearBlind fun i => f (dmGen α h i)) (j : Fin h) (k : ℤ_[2]) (x : (DM α h : Type)) :
    f (dmTauVEquiv α h j k x) = f x := by
  have hU : f (dmGen α h (handleIdxU j)) = 1 := hv.2.1 j
  refine dm_char_fixed f _ (fun i => ?_) x
  by_cases hi : i = handleIdxV j
  · subst hi
    rw [char_dmTauV_handleV α h hA f j k, hU, zpowZtwo_one_base, one_mul]
  · exact char_dmTauV_of_ne α h f j k hi

include hA in
/-- **`τ_c(k)` is invisible to a clear-blind character of `D_M`** — the row that consumes
`f(c̄) = 1` (memo §5.1's `τ_σ` pattern, here with the pivot in the exponent). -/
theorem char_dmTauDEquiv_fixed (f : ContinuousMonoidHom (DM α h : Type) A)
    (hv : IsClearBlind fun i => f (dmGen α h i)) (k : ℤ_[2]) (x : (DM α h : Type)) :
    f (dmTauDEquiv α h k x) = f x := by
  have hC : f (dmC α h) = 1 := hv.1
  refine dm_char_fixed f _ (fun i => ?_) x
  by_cases hi : i = 3
  · subst hi
    rw [show dmGen α h 3 = dmD α h from rfl, char_dmTauD_three α h hA f k, hC,
      zpowZtwo_one_base, one_mul]
  · exact char_dmTauD_of_ne α h f k hi

omit [CompactSpace A] [TotallyDisconnectedSpace A] in
/-- **`Φ_j` is invisible to a clear-blind character of `D_M`** — memo §4's mixing automorphism,
the one generator outside the elementary strata, inside the χ-preserving stabilizer. -/
theorem char_dmMixEquiv_fixed (f : ContinuousMonoidHom (DM α h : Type) A)
    (hv : IsClearBlind fun i => f (dmGen α h i)) (j : Fin h) (x : (DM α h : Type)) :
    f (dmMixEquiv α h j x) = f x := by
  have hC : f (dmGen α h 2) = 1 := hv.1
  have hV : f (dmGen α h (handleIdxV j)) = 1 := hv.2.2 j
  refine dm_char_fixed f _ (fun i => ?_) x
  rw [frame_dmMixEquiv α h j f i]
  by_cases hi : i = handleIdxU j
  · subst hi
    rw [frameMix_handleU_self, hC, hV, mul_one, inv_one, mul_one]
  by_cases h3 : i = 3
  · subst h3
    rw [frameMix_three, hC, hV, one_mul, inv_one, mul_one]
  · rw [frameMix_of_ne _ _ hi h3]

include hA in
/-- **`τ_{v_j}(k)` is invisible to a clear-blind character of `D_N`.** -/
theorem char_dnTauUEquiv_fixed (f : ContinuousMonoidHom (DN α h : Type) A)
    (hv : IsClearBlind fun i => f (dnGen α h i)) (j : Fin h) (k : ℤ_[2]) (x : (DN α h : Type)) :
    f (dnTauUEquiv α h j k x) = f x := by
  have hV : f (dnGen α h (handleIdxV j)) = 1 := hv.2.2 j
  refine dn_char_fixed f _ (fun i => ?_) x
  by_cases hi : i = handleIdxU j
  · subst hi
    rw [char_dnTauU_handleU α h hA f j k, hV, zpowZtwo_one_base, one_mul]
  · exact char_dnTauU_of_ne α h f j k hi

include hA in
/-- **`τ_{u_j}(k)` is invisible to a clear-blind character of `D_N`.** -/
theorem char_dnTauVEquiv_fixed (f : ContinuousMonoidHom (DN α h : Type) A)
    (hv : IsClearBlind fun i => f (dnGen α h i)) (j : Fin h) (k : ℤ_[2]) (x : (DN α h : Type)) :
    f (dnTauVEquiv α h j k x) = f x := by
  have hU : f (dnGen α h (handleIdxU j)) = 1 := hv.2.1 j
  refine dn_char_fixed f _ (fun i => ?_) x
  by_cases hi : i = handleIdxV j
  · subst hi
    rw [char_dnTauV_handleV α h hA f j k, hU, zpowZtwo_one_base, one_mul]
  · exact char_dnTauV_of_ne α h f j k hi

include hA in
/-- **`τ_σ(k)` is invisible to a clear-blind character of `D_N`** — for `N` the pivot letter *is*
`σ`, so this is memo §5.1's `τ_σ` row verbatim. -/
theorem char_dnTauDEquiv_fixed (f : ContinuousMonoidHom (DN α h : Type) A)
    (hv : IsClearBlind fun i => f (dnGen α h i)) (k : ℤ_[2]) (x : (DN α h : Type)) :
    f (dnTauDEquiv α h k x) = f x := by
  have hS : f (dnSigma α h) = 1 := hv.1
  refine dn_char_fixed f _ (fun i => ?_) x
  by_cases hi : i = 3
  · subst hi
    rw [show dnGen α h 3 = dnX2 α h from rfl, char_dnTauD_three α h hA f k, hS,
      zpowZtwo_one_base, one_mul]
  · exact char_dnTauD_of_ne α h f k hi

omit [CompactSpace A] [TotallyDisconnectedSpace A] in
/-- **`Φ_j` is invisible to a clear-blind character of `D_N`.** -/
theorem char_dnMixEquiv_fixed (f : ContinuousMonoidHom (DN α h : Type) A)
    (hv : IsClearBlind fun i => f (dnGen α h i)) (j : Fin h) (x : (DN α h : Type)) :
    f (dnMixEquiv α h j x) = f x := by
  have hS : f (dnGen α h 2) = 1 := hv.1
  have hV : f (dnGen α h (handleIdxV j)) = 1 := hv.2.2 j
  refine dn_char_fixed f _ (fun i => ?_) x
  rw [frame_dnMixEquiv α h j f i]
  by_cases hi : i = handleIdxU j
  · subst hi
    rw [frameMix_handleU_self, hS, hV, mul_one, inv_one, mul_one]
  by_cases h3 : i = 3
  · subst h3
    rw [frameMix_three, hS, hV, one_mul, inv_one, mul_one]
  · rw [frameMix_of_ne _ _ hi h3]

/-! ### The whole of `A(P,h)` at once

`endStabilizer` turns the eight generator rows into a statement about every composite, with no
induction: the blind self-maps form a submonoid, and `Submonoid.closure_le` does the rest. -/

include hA in
/-- **Every element of `A(P,h)` on `D_M` is invisible to a clear-blind character.** -/
theorem dmClearAuts_closure_le (f : ContinuousMonoidHom (DM α h : Type) A)
    (hv : IsClearBlind fun i => f (dmGen α h i)) :
    Submonoid.closure (dmClearAuts α h) ≤ endStabilizer (⇑f) := by
  refine closure_le_endStabilizer _ ?_
  intro E hE
  simp only [dmClearAuts, Set.mem_union, Set.mem_iUnion, Set.mem_range] at hE
  rcases hE with ((⟨j, k, rfl⟩ | ⟨j, k, rfl⟩) | ⟨k, rfl⟩) | ⟨j, rfl⟩
  · exact char_dmTauUEquiv_fixed α h hA f hv j k
  · exact char_dmTauVEquiv_fixed α h hA f hv j k
  · exact char_dmTauDEquiv_fixed α h hA f hv k
  · exact char_dmMixEquiv_fixed α h f hv j

include hA in
/-- **Every element of `A(P,h)` on `D_N` is invisible to a clear-blind character.** -/
theorem dnClearAuts_closure_le (f : ContinuousMonoidHom (DN α h : Type) A)
    (hv : IsClearBlind fun i => f (dnGen α h i)) :
    Submonoid.closure (dnClearAuts α h) ≤ endStabilizer (⇑f) := by
  refine closure_le_endStabilizer _ ?_
  intro E hE
  simp only [dnClearAuts, Set.mem_union, Set.mem_iUnion, Set.mem_range] at hE
  rcases hE with ((⟨j, k, rfl⟩ | ⟨j, k, rfl⟩) | ⟨k, rfl⟩) | ⟨j, rfl⟩
  · exact char_dnTauUEquiv_fixed α h hA f hv j k
  · exact char_dnTauVEquiv_fixed α h hA f hv j k
  · exact char_dnTauDEquiv_fixed α h hA f hv k
  · exact char_dnMixEquiv_fixed α h f hv j

include hA in
/-- The pointwise form on `D_M`: a clear-blind character is fixed by *every* correction the
ν-clearing can produce. -/
theorem char_fixed_of_mem_dmClearAuts (f : ContinuousMonoidHom (DM α h : Type) A)
    (hv : IsClearBlind fun i => f (dmGen α h i))
    {Ψ : ContinuousMulEquiv (DM α h : Type) (DM α h : Type)}
    (hΨ : autEnd Ψ ∈ Submonoid.closure (dmClearAuts α h)) (x : (DM α h : Type)) :
    f (Ψ x) = f x := dmClearAuts_closure_le α h hA f hv hΨ x

include hA in
/-- The pointwise form on `D_N`. -/
theorem char_fixed_of_mem_dnClearAuts (f : ContinuousMonoidHom (DN α h : Type) A)
    (hv : IsClearBlind fun i => f (dnGen α h i))
    {Ψ : ContinuousMulEquiv (DN α h : Type) (DN α h : Type)}
    (hΨ : autEnd Ψ ∈ Submonoid.closure (dnClearAuts α h)) (x : (DN α h : Type)) :
    f (Ψ x) = f x := dnClearAuts_closure_le α h hA f hv hΨ x

end MovedSlots

end ClearBlind

/-! ## §4 The standard-marking rows -/

section StandardRows

variable (α h : ℕ)

/-- **`χ_M` is clear-blind** — MC2's closed form `(A, B, C₀, D) ↦ (1, −1, 1, u)` puts `1` at the
pivot slot and `1` on every handle letter (`chiM_dmC`, `chiM_handleU`, `chiM_handleV`). -/
theorem isClearBlind_chiM : IsClearBlind fun i => chiM α h (dmGen α h i) :=
  ⟨chiM_dmC α h, fun j => chiM_handleU α h j, fun j => chiM_handleV α h j⟩

/-- **`χ_N` is clear-blind** — MC2's closed form `(x₀, x₁, σ, x₂) ↦ (1, v, 1, 1)`; for `N` the
pivot letter is `σ` and `χ_N(σ) = 1`. -/
theorem isClearBlind_chiN : IsClearBlind fun i => chiN α h (dnGen α h i) :=
  ⟨chiN_dnSigma α h, fun j => chiN_handleU α h j, fun j => chiN_handleV α h j⟩

/-- **The marked condition `χ_M ∘ Ψ = χ_M`, for every `Ψ ∈ A(P,h)`.**  This is the χ-half of MC3's
`IsMStabilizer`, discharged for the whole handle stratum. -/
theorem chiM_of_mem_dmClearAuts {Ψ : ContinuousMulEquiv (DM α h : Type) (DM α h : Type)}
    (hΨ : autEnd Ψ ∈ Submonoid.closure (dmClearAuts α h)) (x : (DM α h : Type)) :
    chiM α h (Ψ x) = chiM α h x :=
  char_fixed_of_mem_dmClearAuts α h isProP_two_unitsPadicInt (chiM α h) (isClearBlind_chiM α h)
    hΨ x

/-- **The marked condition `χ_N ∘ Ψ = χ_N`, for every `Ψ ∈ A(P,h)`.** -/
theorem chiN_of_mem_dnClearAuts {Ψ : ContinuousMulEquiv (DN α h : Type) (DN α h : Type)}
    (hΨ : autEnd Ψ ∈ Submonoid.closure (dnClearAuts α h)) (x : (DN α h : Type)) :
    chiN α h (Ψ x) = chiN α h x :=
  char_fixed_of_mem_dnClearAuts α h isProP_two_unitsPadicInt (chiN α h) (isClearBlind_chiN α h)
    hΨ x

/-- The hom-level form on `D_M`: `χ_M ∘ Ψ` **is** `χ_M`, as continuous homs. -/
theorem chiM_comp_of_mem_dmClearAuts {Ψ : ContinuousMulEquiv (DM α h : Type) (DM α h : Type)}
    (hΨ : autEnd Ψ ∈ Submonoid.closure (dmClearAuts α h)) :
    (chiM α h).comp (autHom Ψ) = chiM α h :=
  dm_hom_ext _ _ fun i => chiM_of_mem_dmClearAuts α h hΨ (dmGen α h i)

/-- The hom-level form on `D_N`. -/
theorem chiN_comp_of_mem_dnClearAuts {Ψ : ContinuousMulEquiv (DN α h : Type) (DN α h : Type)}
    (hΨ : autEnd Ψ ∈ Submonoid.closure (dnClearAuts α h)) :
    (chiN α h).comp (autHom Ψ) = chiN α h :=
  dn_hom_ext _ _ fun i => chiN_of_mem_dnClearAuts α h hΨ (dnGen α h i)

end StandardRows

/-! ## §5 The packaged per-family headline

One theorem per rank-four core, bundling HM4's ν-clearing with §4's χ-preservation: **this** is the
statement MC5's certificate cites for the handle stratum.  Both are unconditional in `α` and in the
handle count `h`; the only hypothesis is the ν-side unit row at the pivot, which is memo §5.3's
`ν'(σ̄) ∈ ℤ₂ˣ` for `N` and memo §6.4's residue 2 for `M`. -/

section Headline

variable (α h : ℕ)

/-- **`mHandleMixLift` — the handle stratum for the `M_α` family, as a THEOREM with its marked
condition.**  Memo §1's `MHandleMixHypothesis` binder, restated in memo V5's consumed form
(`ν_P ∈ ν'·A(P,h)` on the handle plane) and *proved*, now carrying the χ-row that MC3's
`IsMStabilizer` demands: for every `Multiplicative ℤ_[2]`-character `ν'` of the core whose value at
the pivot letter `c = C₀` is a 2-adic **unit** there is a continuous automorphism `Ψ` with

* `Ψ ∈ A(P,h)` — a composite of HM2's mixing automorphisms and HM4 §3's exact transvections;
* `χ_M ∘ Ψ = χ_M` — `Ψ` is inside the χ-preserving stabilizer, on the nose;
* `ν'∘Ψ = 1` on every handle letter — the handle plane is cleared;
* `ν'(Ψ c) = ν'(c)` — the pivot is untouched, so the rank-four core solve still sees the same row.

No new axiom, no `B8`, no compactness of `Aut(D_P)`.  What remains after it is the rank-four
**core** block (MC1 §5.1–§5.3, MC3/MC4/G-Lab territory), not the handles. -/
theorem mHandleMixLift (nu' : ContinuousMonoidHom (DM α h : Type) (Multiplicative ℤ_[2]))
    (hc : IsUnit (toAdd (nu' (dmC α h)))) :
    ∃ Ψ : ContinuousMulEquiv (DM α h : Type) (DM α h : Type),
      autEnd Ψ ∈ Submonoid.closure (dmClearAuts α h)
        ∧ (∀ x, chiM α h (Ψ x) = chiM α h x)
        ∧ (∀ j : Fin h, nu' (Ψ (dmGen α h (handleIdxU j))) = 1)
        ∧ (∀ j : Fin h, nu' (Ψ (dmGen α h (handleIdxV j))) = 1)
        ∧ nu' (Ψ (dmC α h)) = nu' (dmC α h) := by
  obtain ⟨Ψ, hmem, hU, hV, h2⟩ := exists_dmClear_nu α h nu' hc
  exact ⟨Ψ, hmem, fun x => chiM_of_mem_dmClearAuts α h hmem x, hU, hV, h2⟩

/-- **`nHandleMixLift` — the handle stratum for the `N_α` family**, the mirror of
`mHandleMixLift`.  For `N` the pivot letter at index `2` is `σ` itself, so the unit row is memo
§5.3's `ν'(σ̄) ∈ ℤ₂ˣ` verbatim. -/
theorem nHandleMixLift (nu' : ContinuousMonoidHom (DN α h : Type) (Multiplicative ℤ_[2]))
    (hc : IsUnit (toAdd (nu' (dnSigma α h)))) :
    ∃ Ψ : ContinuousMulEquiv (DN α h : Type) (DN α h : Type),
      autEnd Ψ ∈ Submonoid.closure (dnClearAuts α h)
        ∧ (∀ x, chiN α h (Ψ x) = chiN α h x)
        ∧ (∀ j : Fin h, nu' (Ψ (dnGen α h (handleIdxU j))) = 1)
        ∧ (∀ j : Fin h, nu' (Ψ (dnGen α h (handleIdxV j))) = 1)
        ∧ nu' (Ψ (dnSigma α h)) = nu' (dnSigma α h) := by
  obtain ⟨Ψ, hmem, hU, hV, h2⟩ := exists_dnClear_nu α h nu' hc
  exact ⟨Ψ, hmem, fun x => chiN_of_mem_dnClearAuts α h hmem x, hU, hV, h2⟩

/-- **`mHandleMixLift` in the memo's own phrasing**: `ν'∘Ψ` **is** the standard marking `ν_M` on
every handle letter (`ν_M` is `0` there — HM4's `nuM_handleU`/`nuM_handleV`). -/
theorem mHandleMixLift_eq_nuM (hα : 1 ≤ α)
    (nu' : ContinuousMonoidHom (DM α h : Type) (Multiplicative ℤ_[2]))
    (hc : IsUnit (toAdd (nu' (dmC α h)))) :
    ∃ Ψ : ContinuousMulEquiv (DM α h : Type) (DM α h : Type),
      autEnd Ψ ∈ Submonoid.closure (dmClearAuts α h)
        ∧ (∀ x, chiM α h (Ψ x) = chiM α h x)
        ∧ (∀ j : Fin h, nu' (Ψ (dmGen α h (handleIdxU j)))
            = nuM α h hα (dmGen α h (handleIdxU j)))
        ∧ (∀ j : Fin h, nu' (Ψ (dmGen α h (handleIdxV j)))
            = nuM α h hα (dmGen α h (handleIdxV j)))
        ∧ nu' (Ψ (dmC α h)) = nu' (dmC α h) := by
  obtain ⟨Ψ, hmem, hchi, hU, hV, h2⟩ := mHandleMixLift α h nu' hc
  exact ⟨Ψ, hmem, hchi, fun j => (hU j).trans (nuM_handleU α h hα j).symm,
    fun j => (hV j).trans (nuM_handleV α h hα j).symm, h2⟩

/-- **`nHandleMixLift` in the memo's own phrasing.** -/
theorem nHandleMixLift_eq_nuN (nu' : ContinuousMonoidHom (DN α h : Type) (Multiplicative ℤ_[2]))
    (hc : IsUnit (toAdd (nu' (dnSigma α h)))) :
    ∃ Ψ : ContinuousMulEquiv (DN α h : Type) (DN α h : Type),
      autEnd Ψ ∈ Submonoid.closure (dnClearAuts α h)
        ∧ (∀ x, chiN α h (Ψ x) = chiN α h x)
        ∧ (∀ j : Fin h, nu' (Ψ (dnGen α h (handleIdxU j))) = nuN α h (dnGen α h (handleIdxU j)))
        ∧ (∀ j : Fin h, nu' (Ψ (dnGen α h (handleIdxV j))) = nuN α h (dnGen α h (handleIdxV j)))
        ∧ nu' (Ψ (dnSigma α h)) = nu' (dnSigma α h) := by
  obtain ⟨Ψ, hmem, hchi, hU, hV, h2⟩ := nHandleMixLift α h nu' hc
  exact ⟨Ψ, hmem, hchi, fun j => (hU j).trans (nuN_handleU α h j).symm,
    fun j => (hV j).trans (nuN_handleV α h j).symm, h2⟩

/-! ### The unit row is satisfiable

HM4 records `isUnit_nuM_dmC`/`isUnit_nuN_dnSigma`: the *standard* markings sit at `1` on the pivot.
Feeding them to the headline shows the hypothesis set is non-empty at every `(α, h)` — memo §6.4's
residue 2 is therefore a question about a **transported** `ν' = ν_K∘f`, not about `ν_P`. -/

theorem mHandleMixLift_nuM (hα : 1 ≤ α) :
    ∃ Ψ : ContinuousMulEquiv (DM α h : Type) (DM α h : Type),
      autEnd Ψ ∈ Submonoid.closure (dmClearAuts α h)
        ∧ (∀ x, chiM α h (Ψ x) = chiM α h x)
        ∧ (∀ j : Fin h, nuM α h hα (Ψ (dmGen α h (handleIdxU j))) = 1)
        ∧ (∀ j : Fin h, nuM α h hα (Ψ (dmGen α h (handleIdxV j))) = 1)
        ∧ nuM α h hα (Ψ (dmC α h)) = nuM α h hα (dmC α h) :=
  mHandleMixLift α h (nuM α h hα) (isUnit_nuM_dmC α h hα)

theorem nHandleMixLift_nuN :
    ∃ Ψ : ContinuousMulEquiv (DN α h : Type) (DN α h : Type),
      autEnd Ψ ∈ Submonoid.closure (dnClearAuts α h)
        ∧ (∀ x, chiN α h (Ψ x) = chiN α h x)
        ∧ (∀ j : Fin h, nuN α h (Ψ (dnGen α h (handleIdxU j))) = 1)
        ∧ (∀ j : Fin h, nuN α h (Ψ (dnGen α h (handleIdxV j))) = 1)
        ∧ nuN α h (Ψ (dnSigma α h)) = nuN α h (dnSigma α h) :=
  nHandleMixLift α h (nuN α h) (isUnit_nuN_dnSigma α h)

end Headline

end MarkedCore

end Dyadic

end GQ2
