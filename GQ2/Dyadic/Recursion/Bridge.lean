/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Opus-4.8 and Fable-5
-/
import GQ2.Dyadic.Recursion.Induction
import GQ2.RadicalEdge.Bridge
import GQ2.Half139Local

/-!
# The radical-edge bridge at the `K`-boundary (dyadic campaign, ticket SD-R3)

Clone of the **`b`-typed layer** of `GQ2/RadicalEdge/Bridge.lean` (198 ln), re-typed at the
general `K`-boundary, with the (139) multiplicity parameterized (memo §4.1(b)).

## Boundary-free below the clone (consumed by import)

`RecursionFrame.piBCiso` (`:51`), `piBCiso_mk` (`:58`) and `piBCisoSymm` (`:153`) mention no
boundary datum at all — they are the model's, used here as `RF.piBCiso` / `RF.piBCisoSymm`.
That is 3 of the model's 10 declarations, and the whole `B/M ≅ C` connecting-iso layer.

## `LiftsOverK` is imported, not redefined

SD-R2 landed `LiftsOverK` early in `Induction.lean:165` (it is needed to *state*
`mStage_partitionK`), with a budget note asking SD-R3 to import it.  Honored: this file imports
it and there is exactly one `LiftsOverK` in the tree.  Everything else in the model's bridge
vocabulary (`CentralOver`, `zBCfibreEquiv`, `rhoPrime`, the two transport equivs) lands here.

## Parameterization delta versus the `ℚ₂` model

`half139_ofK` carries the (139) multiplicity as an opaque `(mM : ℕ)` in place of the model's
literal `(Nat.card ↥RF.MB) ^ 2` — memo §4.1(b), the `SN.mMult (Nat.card ↥RF.MB)` field at
instantiation.  It is threaded, never inspected: the model's proof rewrites `hMcount` in and
finishes with `Finset.sum_const`, which is value-opaque, so the proof is verbatim.  The shape
matches `RecursionInputsK.half139` (`Recursion.lean:457`) on the nose.

`rhoPrime_surjectiveK` clones `GQ2.SectionEight.rhoPrime_surjective`
(`GQ2/Half139Local.lean:47`).  ⚠ Budget note: that lemma lives in a `*Local`-named file but is
**not** `*Local`-class — it is generic in `Γ` and `b`-typed, i.e. spine housed in an
instantiation file.  The `AbsGalQ2` grep (SD-R2's budget rule) correctly flags `Half139Local.lean`
as 40-mention instantiation territory; this one declaration is the exception, and it is cloned
here rather than in the ASK supply package.

Plain-import (memo §5).

Axioms: none beyond std-3.  Print check performed for every declaration in this file: each
prints `[propext, Classical.choice, Quot.sound]`, equal to its model's print — hence a subset.
-/

open scoped Classical

namespace GQ2.Dyadic

open GQ2 GQ2.SectionEight

variable {H E : Type} [Group H] [TopologicalSpace H] [DiscreteTopology H] [Finite H]
  [CommGroup E] [TopologicalSpace E] [DiscreteTopology E] [Finite E]
variable {Y : Type} [Group Y] [TopologicalSpace Y] [DiscreteTopology Y] [Finite Y]
  {T : MarkedTarget H E Y} {Blk : SectionSeven.MinimalBlock T.LY}
variable {q : ℕ} {P : ProfiniteGrp} {nuP : ContinuousMonoidHom P Ztwo}
variable {Γ : Type} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
variable (RF : RecursionFrame T Blk)
variable (b : ContinuousMonoidHom Γ ↥(boundarySubgroupQ q nuP)) (F : BoundaryFrameK q P H E)

/-! ## The `λ`-compatible lifts and the `zBC` fibration -/

/-- **The `λ`-compatible (central) `B`-lifts over `ρ`** at the `K`-boundary: those lifting
through the scalar cover `p_λ`.  Clone of `GQ2.SectionEight.RecursionFrame.CentralOver`
(`GQ2/RadicalEdge/Bridge.lean:76`) — verbatim, over the imported `LiftsOverK`. -/
def CentralOverK (l : RF.DR) (h : l ≠ RF.zeroDR) (ρ : BoundaryLiftsK b F RF.TC) : Type :=
  {m : LiftsOverK RF b F ρ // ∃ g : ContinuousMonoidHom Γ (RF.scalarCover l h).cover,
    ∀ γ : Γ, (RF.scalarCover l h).p (g γ) = m.1.1 γ}

/-- **The `zBC` fibre over `ρ` is `CentralOverK ρ`** at the `K`-boundary.  Clone of
`RecursionFrame.zBCfibreEquiv` (`GQ2/RadicalEdge/Bridge.lean:83`) — verbatim; the redundant
`IsBoundaryLiftK` clause is discharged by SD-R1's `isBoundaryLiftK_of_over`
(`Recursion.lean:138`). -/
noncomputable def zBCfibreEquivK (l : RF.DR) (h : l ≠ RF.zeroDR)
    (ρ : BoundaryLiftsK b F RF.TC) :
    {x : {pr : BoundaryLiftsK b F RF.TC × ContinuousMonoidHom Γ RF.YB //
        (∀ γ : Γ, RF.piBC (pr.2 γ) = pr.1.1.1 γ) ∧ IsBoundaryLiftK b F RF.TB pr.2 ∧
          ∃ g : ContinuousMonoidHom Γ (RF.scalarCover l h).cover,
            ∀ γ : Γ, (RF.scalarCover l h).p (g γ) = pr.2 γ} // x.1.1 = ρ}
      ≃ CentralOverK RF b F l h ρ where
  toFun x :=
    ⟨⟨x.1.1.2, fun γ => by rw [x.1.2.1 γ, x.2]⟩, x.1.2.2.2⟩
  invFun m :=
    ⟨⟨⟨ρ, m.1.1⟩, fun γ => m.1.2 γ,
        isBoundaryLiftK_of_over RF b F m.1.1 ρ m.1.2, m.2⟩, rfl⟩
  left_inv x := by
    obtain ⟨⟨⟨ρ', m⟩, hcompat, hbd, hg⟩, rfl⟩ := x
    rfl
  right_inv m := rfl

omit [TopologicalSpace Y] [DiscreteTopology Y] in
/-- **The (139) half count** at the `K`-boundary, at an opaque multiplicity `mM`.  Clone of
`RecursionFrame.half139_of` (`GQ2/RadicalEdge/Bridge.lean:110`); the model's literal
`(Nat.card ↥RF.MB) ^ 2` becomes the parameter `mM` (memo §4.1(b) — `SN.mMult (Nat.card ↥RF.MB)`
at instantiation).  The multiplicity is threaded and never inspected, so the proof is verbatim.

The conclusion is the `RecursionInputsK.half139` field (`Recursion.lean:457`) on the nose. -/
theorem half139_ofK [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    (hfg : ∃ s : Finset Γ, (Subgroup.closure (s : Set Γ)).topologicalClosure = ⊤)
    (l : RF.DR) (h : l ≠ RF.zeroDR) (mM : ℕ)
    (hlem86 : ∀ ρ : BoundaryLiftsK b F RF.TC,
      2 * Nat.card (CentralOverK RF b F l h ρ) = Nat.card (LiftsOverK RF b F ρ))
    (hMcount : ∀ ρ : BoundaryLiftsK b F RF.TC,
      Nat.card (LiftsOverK RF b F ρ) = mM) :
    2 * zBCK RF b F l h = mM * exactImageCountK b F RF.TC := by
  classical
  haveI : Finite (ContinuousMonoidHom Γ RF.YB) := finite_continuousMonoidHom hfg RF.YB
  haveI : Finite (BoundaryLiftsK b F RF.TC) := finite_boundaryLiftsK b F RF.TC hfg
  haveI : Fintype (BoundaryLiftsK b F RF.TC) := Fintype.ofFinite _
  haveI : Finite (BoundaryLiftsK b F RF.TC × ContinuousMonoidHom Γ RF.YB) := inferInstance
  -- fibration of `zBC` over the `C`-image `ρ`
  have hfib : zBCK RF b F l h
      = ∑ ρ : BoundaryLiftsK b F RF.TC, Nat.card (CentralOverK RF b F l h ρ) := by
    rw [zBCK]
    haveI : Finite {pr : BoundaryLiftsK b F RF.TC × ContinuousMonoidHom Γ RF.YB //
        (∀ γ : Γ, RF.piBC (pr.2 γ) = pr.1.1.1 γ) ∧ IsBoundaryLiftK b F RF.TB pr.2 ∧
          ∃ g : ContinuousMonoidHom Γ (RF.scalarCover l h).cover,
            ∀ γ : Γ, (RF.scalarCover l h).p (g γ) = pr.2 γ} := Subtype.finite
    rw [Nat.card_congr (Equiv.sigmaFiberEquiv (fun x => x.1.1)).symm, Nat.card_sigma]
    exact Finset.sum_congr rfl (fun ρ _ => Nat.card_congr (zBCfibreEquivK RF b F l h ρ))
  calc 2 * zBCK RF b F l h
      = ∑ ρ : BoundaryLiftsK b F RF.TC, 2 * Nat.card (CentralOverK RF b F l h ρ) := by
        rw [hfib, Finset.mul_sum]
    _ = ∑ ρ : BoundaryLiftsK b F RF.TC, Nat.card (LiftsOverK RF b F ρ) :=
        Finset.sum_congr rfl (fun ρ _ => hlem86 ρ)
    _ = ∑ _ρ : BoundaryLiftsK b F RF.TC, mM :=
        Finset.sum_congr rfl (fun ρ _ => hMcount ρ)
    _ = mM * exactImageCountK b F RF.TC := by
        simp only [Finset.sum_const, Finset.card_univ, smul_eq_mul, exactImageCountK,
          Nat.card_eq_fintype_card]
        ring

/-! ## The `MLifts` transport

`LiftsOverK ρ` and `CentralOverK ρ` are the central-obstruction framework's `MLifts` and their
central relation for the datum `En.radData l h`, over the transported lower map
`ρ' := piBCiso⁻¹ ∘ ρ`.  `RF.piBCisoSymm` is boundary-free and is the model's, by import. -/

/-- The transport `ρ' := piBCiso⁻¹ ∘ ρ` at the `K`-boundary.  Clone of
`RecursionFrame.rhoPrime` (`GQ2/RadicalEdge/Bridge.lean:159`). -/
noncomputable def rhoPrimeK (D : RadicalCoverData RF.YB) (hD : D.M = RF.MB)
    (ρ : BoundaryLiftsK b F RF.TC) : ContinuousMonoidHom Γ (RF.YB ⧸ D.M) :=
  (RF.piBCisoSymm D hD).comp ρ.1.1

omit [TopologicalSpace Y] [DiscreteTopology Y] [IsTopologicalGroup Γ] in
/-- Clone of `RecursionFrame.rhoPrime_apply` (`GQ2/RadicalEdge/Bridge.lean:164`). -/
theorem rhoPrimeK_apply (D : RadicalCoverData RF.YB) (hD : D.M = RF.MB)
    (ρ : BoundaryLiftsK b F RF.TC) (γ : Γ) :
    rhoPrimeK RF b F D hD ρ γ = (RF.piBCiso D hD).symm (ρ.1.1 γ) := rfl

omit [TopologicalSpace Y] [DiscreteTopology Y] [IsTopologicalGroup Γ] in
/-- **`ρ'` is surjective** at the `K`-boundary.  Clone of
`GQ2.SectionEight.rhoPrime_surjective` (`GQ2/Half139Local.lean:47`) — see the header's budget
note: spine housed in an instantiation-named file. -/
theorem rhoPrimeK_surjective (D : RadicalCoverData RF.YB) (hD : D.M = RF.MB)
    (ρ : BoundaryLiftsK b F RF.TC) :
    Function.Surjective (rhoPrimeK RF b F D hD ρ) := fun y => by
  obtain ⟨γ, hγ⟩ := ρ.1.2 (RF.piBCiso D hD y)
  exact ⟨γ, by rw [rhoPrimeK_apply, hγ, MulEquiv.symm_apply_apply]⟩

/-- **The `LiftsOverK ↔ MLifts` bridge** at the `K`-boundary.  Clone of
`RecursionFrame.liftsOver_equiv` (`GQ2/RadicalEdge/Bridge.lean:171`) — verbatim. -/
def liftsOverK_equiv (D : RadicalCoverData RF.YB) (hD : D.M = RF.MB)
    (ρ : BoundaryLiftsK b F RF.TC) :
    LiftsOverK RF b F ρ ≃ MLifts D (rhoPrimeK RF b F D hD ρ) :=
  Equiv.subtypeEquivRight fun m => by
    refine ⟨fun hover γ => ?_, fun hmk γ => ?_⟩
    · show QuotientGroup.mk (m γ) = (RF.piBCiso D hD).symm (ρ.1.1 γ)
      rw [← hover γ, ← RF.piBCiso_mk D hD, MulEquiv.symm_apply_apply]
    · rw [← RF.piBCiso_mk D hD (m γ), hmk γ, rhoPrimeK_apply, MulEquiv.apply_symm_apply]

/-- **The `CentralOverK ↔ central `MLifts`** bridge** at the `K`-boundary.  Clone of
`RecursionFrame.centralOver_equiv` (`GQ2/RadicalEdge/Bridge.lean:183`) — verbatim. -/
def centralOverK_equiv (l : RF.DR) (h : l ≠ RF.zeroDR) (D : RadicalCoverData RF.YB)
    (hD : D.M = RF.MB) (hC : D.C = RF.scalarCover l h) (ρ : BoundaryLiftsK b F RF.TC) :
    CentralOverK RF b F l h ρ ≃ {f : MLifts D (rhoPrimeK RF b F D hD ρ) // f.Central} :=
  Equiv.subtypeEquiv (liftsOverK_equiv RF b F D hD ρ) fun m => by
    rw [← hC]; exact Iff.rfl

/-! ## The `n = 1` refl-bridges -/

section RegressionN1

omit [TopologicalSpace Y] [DiscreteTopology Y] [IsTopologicalGroup Γ] in
/-- At `n = 1` the `λ`-compatible lift set **is** the model's — `rfl`. -/
theorem centralOverK_eq (b : ContinuousMonoidHom Γ ↥(boundarySubgroupQ 2 nuTwo))
    (F : BoundaryFrameK 2 PiBd H E) (l : RF.DR) (h : l ≠ RF.zeroDR)
    (ρ : BoundaryLiftsK b F RF.TC) :
    CentralOverK RF b F l h ρ = RF.CentralOver b F.toBoundaryFrame l h ρ := rfl

omit [TopologicalSpace Y] [DiscreteTopology Y] [IsTopologicalGroup Γ] in
/-- At `n = 1` the transported lower map **is** the model's — `rfl`. -/
theorem rhoPrimeK_eq (b : ContinuousMonoidHom Γ ↥(boundarySubgroupQ 2 nuTwo))
    (F : BoundaryFrameK 2 PiBd H E) (D : RadicalCoverData RF.YB) (hD : D.M = RF.MB)
    (ρ : BoundaryLiftsK b F RF.TC) :
    rhoPrimeK RF b F D hD ρ = RF.rhoPrime b F.toBoundaryFrame D hD ρ := rfl

end RegressionN1

end GQ2.Dyadic
