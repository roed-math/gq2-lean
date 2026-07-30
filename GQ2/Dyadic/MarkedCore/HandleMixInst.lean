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

end MovedSlots

end ClearBlind

end MarkedCore

end Dyadic

end GQ2
