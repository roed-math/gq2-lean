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
discharge, implementing `docs/dyadic/handlemixlift-spike.md` §7's fifth row as **reduced** by HM4's
finding.  The memo budgeted HM5 as "the `M`/`N` instantiations (`Φ^M_j`, the `N` variant) —
mechanical re-instantiation of HM2/HM3"; HM2's family swap made one definition serve both rank-four
cores, so HM2, HM3 and HM4 are already `M`- *and* `N`-uniform at general `(α, h)` and there is
nothing to re-instantiate.  What was actually left, and is what this file lands, is the **χ-side**:
HM4 clears `ν` but says nothing about the orientation, and MC3's `IsMStabilizer` is a *χ-preserving*
cup isometry — so the corrections HM4 produces have to be shown to lie inside the χ-stabilizer
before MC5 may use them.  They do, on the nose.

Repo conventions as upstream: `x ^ g = g⁻¹xg` (`GQ2.conjP`), `[x,y] = x⁻¹y⁻¹xy` (`GQ2.commP`), and
HM1's naming rule for the `τ` family (a Lean name's suffix is the letter that MOVES).

## The χ-truth, in one paragraph

Every generator of `A(P,h)` moves at most two slots of the frame, and it moves them by the value at
the **pivot** slot — index `2`, the letter `c = C₀` for `M` and `σ` for `N` — or by the partner
handle value:

```
τ_{v_j}(k) : ū_j ↦ ū_j + k·v̄_j        τ_c(k) : d̄ ↦ d̄ + k·c̄
τ_{u_j}(k) : v̄_j ↦ v̄_j + k·ū_j        Φ_j    : d̄ ↦ d̄ + (c̄ − v̄_j),  ū_j ↦ ū_j + (c̄ − v̄_j)
```

Read against `ν` this is HM4: the pivot value `ν'(c̄)` is a **unit**, so the handle slots are fully
steerable and the plane can be annihilated.  Read against `χ` it is this file: the pivot value
`χ_P(c̄)` is **trivial** and `χ_P ≡ 1` on the handle plane, so every one of the moves is the
identity on `χ_P`.  **One slot, read additively and multiplicatively** — that complementarity is
why the handle stratum lands inside the χ-preserving stabilizer for free, and it is the finding of
this ticket.

The rows are stated **honestly**, for an arbitrary character `f` rather than only for MC2's
standard `χ_M`/`χ_N`: `IsClearBlind` isolates the hypothesis (`f` trivial at the pivot and on the
handle plane) and §3 records the *exact* action in each case, so the failure mode is visible.  It
is a real failure mode: for a general character `Φ_j` multiplies **both** `f(d̄)` and `f(ū_j)` by
the single factor `f(c̄)·f(v̄_j)⁻¹`, and `τ_c(k)` multiplies `f(d̄)` by `f(c̄)^k`, so a character
with `f(c̄) ≠ f(v̄_j)` is genuinely *moved* by the mixing element.  Nothing here is forced by the
relator; it is a property of MC2's closed forms `(A,B,C₀,D) ↦ (1,−1,1,u)` and
`(x₀,x₁,σ,x₂) ↦ (1,v,1,1)`, both of which put `1` at the pivot (`isClearBlind_chiM`,
`isClearBlind_chiN`).  A *transported* orientation `χ' = χ_K∘f` must therefore be checked, not
assumed — the χ-side twin of memo §6.4's residue 2.

## Contents

* **§1 Precomposition stabilizers.**  `endStabilizer g` — the self-maps of `X` that `g` cannot
  see — as a *submonoid* of `Function.End X`, plus `closure_le_endStabilizer`.  This is what
  replaces a closure induction: HM4 needed `Submonoid.closure_induction` for the realization
  bridge because the conclusion there was existential, whereas χ-invariance is a submonoid
  membership and `Submonoid.closure_le` closes it in one line.

* **§2 `autHom`** (a continuous automorphism read as a continuous endomorphism, HM4 §4's
  `⟨Ψ.toMonoidHom, …⟩` idiom named once) and `dm_char_fixed`/`dn_char_fixed`: a character fixed on
  the marked generators is fixed everywhere (MC2's `dm_hom_ext`/`dn_hom_ext`).

* **§3 The exact character rows.**  `IsClearBlind`, the six untouched-slot rows (no hypothesis, no
  pro-2 structure on the target), the six moved-slot rows (`char_dmTauU_handleU`, …, needing
  `map_zpowZtwo`, hence a pro-2 target), the eight `_fixed` rows, and then
  `dmClearAuts_closure_le`/`dnClearAuts_closure_le`: **all of `A(P,h)` at once**.  `Φ_j`'s two
  moved rows are not restated — HM3's `frame_dmMixEquiv_dmD`/`_handleU` and the `N`-mirrors already
  hold for an arbitrary character into a commutative group.  The section closes with the *negative*
  rows `char_dmMixEquiv_ne`/`char_dnMixEquiv_ne`: blindness is a genuine hypothesis, and `Φ_j` moves
  every character whose pivot value differs from `f(v̄_j)`.

* **§4 The standard-marking rows.**  `isClearBlind_chiM`, `isClearBlind_chiN`; the eight
  generator-by-generator rows (`chiM_dmMixEquiv`, `chiM_dmTauUEquiv`, … and the `N`-mirrors) —
  the memo's per-family instantiations, evaluated at MC2's closed forms; and the marked condition
  `χ_P ∘ Ψ = χ_P` for every `Ψ ∈ A(P,h)` in pointwise (`chiM_of_mem_dmClearAuts`,
  `chiN_of_mem_dnClearAuts`) and hom form (`chiM_comp_of_mem_dmClearAuts`,
  `chiN_comp_of_mem_dnClearAuts`).

* **§5 The headline, per family.**  `mHandleMixLift` and `nHandleMixLift` bundle HM4's
  `exists_dmClear_nu`/`exists_dnClear_nu` **with** the χ-row: one existential carrying membership in
  `A(P,h)`, `χ_P ∘ Ψ = χ_P`, `ν'∘Ψ = 1` on the whole handle plane, and `ν'(Ψ c) = ν'(c)`.  These
  are the statements MC5's certificate cites for the handle stratum.  `*_eq_nuM`/`*_eq_nuN` restate
  the ν-rows in memo V5's phrasing (`ν'∘Ψ` **is** `ν_P` there), and `*_nuM`/`*_nuN` instantiate the
  unit row at MC2's standard markings, so the hypothesis set is visibly non-empty at every
  `(α, h)`.

* **§6 Small-instance pins.**  A `StressTests` section of `example`s at `(α, h) = (2, 1)` — the
  smallest instance with both a non-trivial orientation unit and a non-empty handle plane.  It pins
  both directions: `Φ_j` fixes `χ_M`, and `Φ_j` **moves** `ν_M` on the `d̄`-slot.

## The lane, closed: HM1 → HM5

* **HM1** `HandleMix.lean` — handle-block splitting, the two commutator expansions, the exact
  transvections for **2-adic** exponents.
* **HM2** `HandleMixEquiv.lean` — `Φ_j` as an honest `ContinuousMulEquiv` of both cores, with
  `Φ_j(P) = P` on the nose and an explicit inverse.
* **HM3** `HandleMixFrame.lean` — the frame calculus: the Eichler elements, `N² = 0`, the
  `θ_w`-conjugation reaching every 2-adic coefficient, `SL₂ = E₂` over `ℤ₂`, the ν-frame
  dictionary.
* **HM4** `HandleMixClear.lean` — `A(P,h)` at both levels, the ν-clearing, the realization
  bridge, **the restated obligation as a theorem**, MC5's `hLift` split three ways.
* **HM5** this file — the χ-side: `A(P,h)` sits inside the χ-stabilizer, and the two packaged
  headlines.

**THEOREM (not a binder):** the handle stratum of `HandleMixLift` for the `M_α` and `N_α`
families — memo §1's `MHandleMixHypothesis`/`NHandleMixHypothesis` in memo V5's consumed form,
`ν_P ∈ ν'·A(P,h)` on the handle plane, **together with** the χ-preservation the marked stabilizer
condition requires.  At general `α`, general handle count `h`, with no new axiom, **no B8**
(`peripheralCyclotomicAction`), **no B3c** (`dyadicOrientation` — MC2's `χ_M`/`χ_N` are
combinatorial closed forms, not the arithmetic orientation), and no appeal to compactness of
`Aut(D_P)`.  Every declaration in this file prints at the standard three axioms.

**Still a binder:** MC1 §5.3's S3 core↔core mixing at rank four (`MCoreMixHypothesis`,
`NCoreMixHypothesis` — MC1 §8 Decision 2, G-Lab territory; memo §6.5's HM6 spike, owner-held, would
turn the `N` instance into a theorem), and MC1 §5.1–§5.2's S1 ∪ S2 Nielsen-and-scaling stratum
(`MNielsenScalingHypothesis`, `NNielsenScalingHypothesis` — MC3/MC4's to construct, the scalings
through the *existing* axiom B8).  Both are HM4 §6's fields, untouched here.

## The two items this ticket defers

1. **The L-family instantiation.**  Memo §1.2 lists the L collector/`L_tw` and `L_sq` alongside
   `M`/`N`, and memo §6.2 marks the collector as covered by the same construction.  Its core is
   **not** `DM`/`DN` — it lives in `GQ2/Dyadic/SqCore/` — so the instantiation is not a
   re-parametrisation of this file but a fresh application of HM1–HM3 in that frame, and it is
   blocked on a *correction*: SQ1 sharpened memo §6.3's residue 1 into `docs/dyadic/sq-design.md`
   §7 **R1**, which shows S2.4 §1.1's "`χ(σ) = 1` for type L" is **false** for `L_sq`
   (`χ_sq(σ) = S`, of infinite order).  In this file's vocabulary that says exactly that the `L_sq`
   pivot is **not clear-blind**: the χ-trivial subspace of the `L_sq` frame is a rank-1 free
   `ℤ₂`-module transverse to `σ̄`, not `⟨σ̄⟩ ⊕ P_han`, so §3's blindness hypothesis fails at the
   pivot and the reachable-block identification of memo §6.4 has to be redone there.  The R1 verdict
   assigns that redo to MC5; nothing in this file speaks to `L_sq`.

2. **The `M`-side transported ν-row.**  Memo §6.4's residue 2 (owner question Q2): is `ν'(c̄)` a
   unit for the `M_α` marked data?  HM4 settled the *standard* marking (`isUnit_nuM_dmC`) and §5
   here re-exports it (`mHandleMixLift_nuM`), so the headline is never vacuous; but the `ν'` MC5
   actually feeds it is the **transported** `ν_K∘f`, and whether its pivot value is a unit is a
   property of the marked data `(C,I,λ,γ)`, decided once F4/MC5 have the `M` ν-row.  If the unit
   sits on `d̄` and not on `c̄`, the clearing would need elements moving `c`, which the `c^{2^α}`
   factor forbids, and `M` falls back to memo §1's binder — `N` is unaffected, its pivot being `σ`.
   One line to check, not a proof obligation, and it is the *only* hypothesis either headline takes.
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

/-! ## §3 The exact character action of the four clearing generator families -/

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

/-! ### Every generator of `A(P,h)` is invisible to a clear-blind character

`Φ_j`'s two moved rows need no restating: HM3's `frame_dmMixEquiv_dmD`, `frame_dmMixEquiv_handleU`
and their `N`-mirrors already hold for an arbitrary character into a commutative group, and they say
that both moved slots pick up the **same** factor `f(c̄)·f(v̄_j)⁻¹`.  So `Φ_j` is invisible to `f`
exactly when that factor is `1` — which `IsClearBlind` gives, and which a general character need
**not** satisfy.

The pattern is then the same eight times: `dm_char_fixed`/`dn_char_fixed` reduce to the marked
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

/-! ### The rows are not automatic

The converse direction, stated so that nothing above is over-read: `Φ_j` moves the `d̄`-slot of
*any* character whose pivot value differs from the partner handle value.  Blindness is a genuine
hypothesis, not a formality — for the ν-side characters HM4 steers, it is exactly false, which is
why the clearing works at all (`nuM 2 1 _ (dmC 2 1) = ofAdd 1 ≠ ofAdd 0`; §6 pins it). -/

/-- **`Φ_j` genuinely moves a character whose pivot value differs from `f(v̄_j)`.** -/
theorem char_dmMixEquiv_ne (f : ContinuousMonoidHom (DM α h : Type) A) (j : Fin h)
    (hne : f (dmC α h) ≠ f (dmGen α h (handleIdxV j))) :
    f (dmMixEquiv α h j (dmD α h)) ≠ f (dmD α h) := by
  rw [frame_dmMixEquiv_dmD α h j f]
  intro hcontra
  rw [mul_inv_eq_iff_eq_mul, mul_comm (f (dmD α h))] at hcontra
  exact hne (mul_right_cancel hcontra)

/-- The `N`-mirror of `char_dmMixEquiv_ne`. -/
theorem char_dnMixEquiv_ne (f : ContinuousMonoidHom (DN α h : Type) A) (j : Fin h)
    (hne : f (dnSigma α h) ≠ f (dnGen α h (handleIdxV j))) :
    f (dnMixEquiv α h j (dnX2 α h)) ≠ f (dnX2 α h) := by
  rw [frame_dnMixEquiv_dnX2 α h j f]
  intro hcontra
  rw [mul_inv_eq_iff_eq_mul, mul_comm (f (dnX2 α h))] at hcontra
  exact hne (mul_right_cancel hcontra)

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

/-! ### Generator by generator

The memo's per-family instantiation rows, evaluated at MC2's standard orientations: what HM2's
`dmMixEquiv`/`dnMixEquiv` and HM4 §3's three `τ` families do to `χ_P` is **nothing**. -/

theorem chiM_dmTauUEquiv (j : Fin h) (k : ℤ_[2]) (x : (DM α h : Type)) :
    chiM α h (dmTauUEquiv α h j k x) = chiM α h x :=
  char_dmTauUEquiv_fixed α h isProP_two_unitsPadicInt _ (isClearBlind_chiM α h) j k x

theorem chiM_dmTauVEquiv (j : Fin h) (k : ℤ_[2]) (x : (DM α h : Type)) :
    chiM α h (dmTauVEquiv α h j k x) = chiM α h x :=
  char_dmTauVEquiv_fixed α h isProP_two_unitsPadicInt _ (isClearBlind_chiM α h) j k x

theorem chiM_dmTauDEquiv (k : ℤ_[2]) (x : (DM α h : Type)) :
    chiM α h (dmTauDEquiv α h k x) = chiM α h x :=
  char_dmTauDEquiv_fixed α h isProP_two_unitsPadicInt _ (isClearBlind_chiM α h) k x

/-- **`χ_M ∘ Φ_j = χ_M`** — memo §4's mixing automorphism, the generator outside the elementary
strata, preserves the canonical orientation of the `M_α` core. -/
theorem chiM_dmMixEquiv (j : Fin h) (x : (DM α h : Type)) :
    chiM α h (dmMixEquiv α h j x) = chiM α h x :=
  char_dmMixEquiv_fixed α h _ (isClearBlind_chiM α h) j x

theorem chiN_dnTauUEquiv (j : Fin h) (k : ℤ_[2]) (x : (DN α h : Type)) :
    chiN α h (dnTauUEquiv α h j k x) = chiN α h x :=
  char_dnTauUEquiv_fixed α h isProP_two_unitsPadicInt _ (isClearBlind_chiN α h) j k x

theorem chiN_dnTauVEquiv (j : Fin h) (k : ℤ_[2]) (x : (DN α h : Type)) :
    chiN α h (dnTauVEquiv α h j k x) = chiN α h x :=
  char_dnTauVEquiv_fixed α h isProP_two_unitsPadicInt _ (isClearBlind_chiN α h) j k x

theorem chiN_dnTauDEquiv (k : ℤ_[2]) (x : (DN α h : Type)) :
    chiN α h (dnTauDEquiv α h k x) = chiN α h x :=
  char_dnTauDEquiv_fixed α h isProP_two_unitsPadicInt _ (isClearBlind_chiN α h) k x

/-- **`χ_N ∘ Φ_j = χ_N`.** -/
theorem chiN_dnMixEquiv (j : Fin h) (x : (DN α h : Type)) :
    chiN α h (dnMixEquiv α h j x) = chiN α h x :=
  char_dnMixEquiv_fixed α h _ (isClearBlind_chiN α h) j x

/-! ### And all of `A(P,h)` -/

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

/-! ## §6 Small-instance pins

`(α, h) = (2, 1)`: the smallest instance with a genuine unit (`α ≥ 1`, so `u = (1 − 2^α)⁻¹ ≠ 1`)
*and* a genuine handle (`h ≥ 1`, so the handle plane is not empty and `Φ_j` has somewhere to mix
to).  Everything below is an instantiation of a general theorem above — the pins exist so that a
reader can see the statements at concrete numerals, and so that a later reshaping of the general
statements cannot silently become vacuous. -/

section StressTests

/-- The rank of the `(α, 1)` cores is `6`: four core letters and one handle pair. -/
example : coreRank 1 = 6 := by decide

/-- The single handle pair sits at slots `4`, `5`. -/
example : handleIdxU (0 : Fin 1) = (4 : Fin (coreRank 1)) := by decide

example : handleIdxV (0 : Fin 1) = (5 : Fin (coreRank 1)) := by decide

/-- `χ_M` is **not** the trivial character at `α = 2`: it takes the value `u = (1 − 4)⁻¹ ≠ 1` on
`D`.  So the χ-preservation rows above are not preserving nothing. -/
example : chiM 2 1 (dmD 2 1) = mUnit 2 := chiM_dmD 2 1

example : (mUnit 2 : ℤ_[2]ˣ) ≠ 1 := by
  intro hu
  have h1 : (mUnit 2 : ℤ_[2]) * (1 - 2 ^ 2) = 1 := mUnit_mul (by omega)
  rw [hu, Units.val_one, one_mul] at h1
  norm_num at h1

/-- `χ_M` is clear-blind at `(2, 1)`. -/
example : IsClearBlind fun i => chiM 2 1 (dmGen 2 1 i) := isClearBlind_chiM 2 1

/-- `χ_N` is clear-blind at `(2, 1)`. -/
example : IsClearBlind fun i => chiN 2 1 (dnGen 2 1 i) := isClearBlind_chiN 2 1

/-- The mixing automorphism at the single handle is in `A(P,1)`. -/
example : autEnd (dmMixEquiv 2 1 0) ∈ Submonoid.closure (dmClearAuts 2 1) :=
  (dmRealizes_mix 2 1 0).1

/-- **The χ-truth at a concrete instance**: HM2's mixing automorphism — the one generator that is
*not* an elementary Nielsen lift — fixes `χ_M` pointwise. -/
example (x : (DM 2 1 : Type)) : chiM 2 1 (dmMixEquiv 2 1 0 x) = chiM 2 1 x :=
  chiM_dmMixEquiv 2 1 0 x

/-- The `N`-side mirror. -/
example (x : (DN 2 1 : Type)) : chiN 2 1 (dnMixEquiv 2 1 0 x) = chiN 2 1 x :=
  chiN_dnMixEquiv 2 1 0 x

/-- **The other side of the χ-truth, concretely**: the same mixing automorphism *does* move the
standard ν-marking, whose pivot value is the unit `1` rather than `0`.  So `char_dmMixEquiv_ne`'s
hypothesis is satisfiable, blindness is a genuine condition, and the ν-clearing of HM4 has
something to clear. -/
example : nuM 2 1 (by omega) (dmMixEquiv 2 1 0 (dmD 2 1)) ≠ nuM 2 1 (by omega) (dmD 2 1) := by
  refine char_dmMixEquiv_ne 2 1 _ 0 ?_
  rw [nuM_dmC, nuM_handleV]
  exact fun hcontra => absurd (ofAdd_eq_one.mp hcontra) one_ne_zero

example : nuN 2 1 (dnMixEquiv 2 1 0 (dnX2 2 1)) ≠ nuN 2 1 (dnX2 2 1) := by
  refine char_dnMixEquiv_ne 2 1 _ 0 ?_
  rw [nuN_dnSigma, nuN_handleV]
  exact fun hcontra => absurd (ofAdd_eq_one.mp hcontra) one_ne_zero

/-- The ν-side unit row holds for the standard `M` marking at `(2, 1)`. -/
example : IsUnit (toAdd (nuM 2 1 (by omega) (dmC 2 1))) := isUnit_nuM_dmC 2 1 (by omega)

/-- The ν-side unit row holds for the standard `N` marking at `(2, 1)`. -/
example : IsUnit (toAdd (nuN 2 1 (dnSigma 2 1))) := isUnit_nuN_dnSigma 2 1

/-- **The `M`-headline at `(α, h) = (2, 1)`**, written out. -/
example (nu' : ContinuousMonoidHom (DM 2 1 : Type) (Multiplicative ℤ_[2]))
    (hc : IsUnit (toAdd (nu' (dmC 2 1)))) :
    ∃ Ψ : ContinuousMulEquiv (DM 2 1 : Type) (DM 2 1 : Type),
      autEnd Ψ ∈ Submonoid.closure (dmClearAuts 2 1)
        ∧ (∀ x, chiM 2 1 (Ψ x) = chiM 2 1 x)
        ∧ (∀ j : Fin 1, nu' (Ψ (dmGen 2 1 (handleIdxU j))) = 1)
        ∧ (∀ j : Fin 1, nu' (Ψ (dmGen 2 1 (handleIdxV j))) = 1)
        ∧ nu' (Ψ (dmC 2 1)) = nu' (dmC 2 1) := mHandleMixLift 2 1 nu' hc

/-- **The `N`-headline at `(α, h) = (2, 1)`**, written out. -/
example (nu' : ContinuousMonoidHom (DN 2 1 : Type) (Multiplicative ℤ_[2]))
    (hc : IsUnit (toAdd (nu' (dnSigma 2 1)))) :
    ∃ Ψ : ContinuousMulEquiv (DN 2 1 : Type) (DN 2 1 : Type),
      autEnd Ψ ∈ Submonoid.closure (dnClearAuts 2 1)
        ∧ (∀ x, chiN 2 1 (Ψ x) = chiN 2 1 x)
        ∧ (∀ j : Fin 1, nu' (Ψ (dnGen 2 1 (handleIdxU j))) = 1)
        ∧ (∀ j : Fin 1, nu' (Ψ (dnGen 2 1 (handleIdxV j))) = 1)
        ∧ nu' (Ψ (dnSigma 2 1)) = nu' (dnSigma 2 1) := nHandleMixLift 2 1 nu' hc

/-- Both headlines are inhabited at `(2, 1)` by the standard markings. -/
example : ∃ Ψ : ContinuousMulEquiv (DM 2 1 : Type) (DM 2 1 : Type),
    autEnd Ψ ∈ Submonoid.closure (dmClearAuts 2 1)
      ∧ (∀ x, chiM 2 1 (Ψ x) = chiM 2 1 x)
      ∧ (∀ j : Fin 1, nuM 2 1 (by omega) (Ψ (dmGen 2 1 (handleIdxU j))) = 1)
      ∧ (∀ j : Fin 1, nuM 2 1 (by omega) (Ψ (dmGen 2 1 (handleIdxV j))) = 1)
      ∧ nuM 2 1 (by omega) (Ψ (dmC 2 1)) = nuM 2 1 (by omega) (dmC 2 1) :=
  mHandleMixLift_nuM 2 1 (by omega)

example : ∃ Ψ : ContinuousMulEquiv (DN 2 1 : Type) (DN 2 1 : Type),
    autEnd Ψ ∈ Submonoid.closure (dnClearAuts 2 1)
      ∧ (∀ x, chiN 2 1 (Ψ x) = chiN 2 1 x)
      ∧ (∀ j : Fin 1, nuN 2 1 (Ψ (dnGen 2 1 (handleIdxU j))) = 1)
      ∧ (∀ j : Fin 1, nuN 2 1 (Ψ (dnGen 2 1 (handleIdxV j))) = 1)
      ∧ nuN 2 1 (Ψ (dnSigma 2 1)) = nuN 2 1 (dnSigma 2 1) :=
  nHandleMixLift_nuN 2 1

end StressTests

end MarkedCore

end Dyadic

end GQ2
