/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Opus-4.8 and Fable-5
-/
import GQ2.SectionEight
import GQ2.AffineTLift

/-!
# The `zBC ↔ MLifts` bridge and the (139) half count

The nonzero-radical-edge display (139), `2·Z_{Γ,λ}(B/C) = 2^{2·dim M}·e_Γ(C)`, in the
`RecursionInputs.half139` shape `2·zBC = |M_B|²·e_Γ(C)`.

**Strategy** (source-generic; the source's Lemma 8.6 and the `2^{2·dim M}` `M`-lift count
enter as hypotheses, so d6 plugs in `lemma_8_6_local`/`lemma_8_6_gammaA` and the props
5.15/5.16 numerics per source):

1. `zBC` fibres over the lower exact-image map `ρ : Γ ↠ C` (`BoundaryLifts b F T_C`); the
   fibre is the set of `λ`-compatible `B`-lifts over `ρ`, whose `IsBoundaryLift` clause is
   redundant (`RecursionFrame.isBoundaryLift_of_over`, the Prop. 8.9 assembly).
2. Via the iso `B/M ≅ C` (`piBCiso`, from `ker π_{BC} = M_B`), that fibre is exactly the
   central `M`-lifts `{f : MLifts (E.radData l h) ρ' // f.Central}` of the central-obstruction framework/d1 (`Central` =
   lifts through the scalar cover).
3. Lemma 8.6 halves it (`2·#central = #MLifts`); the props 5.15/5.16 count gives
   `#MLifts = |M_B|²`.  Summing over `ρ` and clearing the `2` yields (139).

`half139_of` is the assembled bridge; d6 discharges the two per-source hypotheses.  All
std-3; the axiom budget (B6, B7) enters only through the consumed Lemma 8.6.
-/

namespace GQ2

namespace SectionEight

open scoped Classical

variable {H E : Type} [Group H] [TopologicalSpace H] [DiscreteTopology H] [Finite H]
  [CommGroup E] [TopologicalSpace E] [DiscreteTopology E] [Finite E]
variable {Y : Type} [Group Y] [TopologicalSpace Y] [DiscreteTopology Y] [Finite Y]
  {T : MarkedTarget H E Y} {Blk : SectionSeven.MinimalBlock T.LY}

namespace RecursionFrame

variable (RF : RecursionFrame T Blk)

/-- **The connecting iso** `B/M ≅ C` induced by `π_{BC} : B ↠ C` with `ker = M_B`.  Stated over
a `RadicalCoverData` datum `D` with `D.M = M_B` so the quotient uses **`D.M`'s** normality
instance — matching `MLifts (E.radData l h)` on the nose (avoids the `RF.MB` vs `(E.radData
l h).M` instance-diamond in the transport proofs). -/
noncomputable def piBCiso (D : RadicalCoverData RF.YB) (hD : D.M = RF.MB) :
    (RF.YB ⧸ D.M) ≃* RF.YC :=
  (QuotientGroup.quotientMulEquivOfEq (hD.trans RF.ker_piBC.symm)).trans
    (QuotientGroup.quotientKerEquivOfSurjective RF.piBC RF.piBC_surj)

omit [TopologicalSpace H] [DiscreteTopology H] [Finite H] [TopologicalSpace E]
  [DiscreteTopology E] [Finite E] [TopologicalSpace Y] [DiscreteTopology Y] in
@[simp] theorem piBCiso_mk (D : RadicalCoverData RF.YB) (hD : D.M = RF.MB) (bb : RF.YB) :
    RF.piBCiso D hD (QuotientGroup.mk bb) = RF.piBC bb := by
  rw [piBCiso, MulEquiv.trans_apply]
  rw [show (QuotientGroup.quotientMulEquivOfEq (hD.trans RF.ker_piBC.symm)) (QuotientGroup.mk bb)
      = QuotientGroup.mk bb from rfl]
  exact QuotientGroup.kerLift_mk _ bb

variable {Γ : Type} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
variable (b : ContinuousMonoidHom Γ ↥boundarySubgroup) (F : BoundaryFrame H E)

/-- **All `B`-lifts over a lower exact-image map `ρ : Γ ↠ C`**: continuous homs `Γ → B`
whose `π_{BC}`-image is `ρ`.  (The paper's `M`-lifts over `ρ`; `IsBoundaryLift` is automatic
by `isBoundaryLift_of_over`.) -/
def LiftsOver (ρ : BoundaryLifts b F RF.TC) : Type :=
  {m : ContinuousMonoidHom Γ RF.YB // ∀ γ : Γ, RF.piBC (m γ) = ρ.1.1 γ}

/-- **The `λ`-compatible (central) `B`-lifts over `ρ`**: those lifting through the scalar
cover `p_λ` — the `Central` relation of the central-obstruction framework. -/
def CentralOver (l : RF.DR) (h : l ≠ RF.zeroDR) (ρ : BoundaryLifts b F RF.TC) : Type :=
  {m : LiftsOver RF b F ρ // ∃ g : ContinuousMonoidHom Γ (RF.scalarCover l h).cover,
    ∀ γ : Γ, (RF.scalarCover l h).p (g γ) = m.1.1 γ}

/-- **The `zBC` fibre over `ρ` is `CentralOver ρ`**: eliminating the pair, a `zBC`-datum with
`C`-component `ρ` is exactly a `λ`-compatible `B`-lift over `ρ` (the `IsBoundaryLift` clause is
redundant, `isBoundaryLift_of_over`). -/
noncomputable def zBCfibreEquiv (l : RF.DR) (h : l ≠ RF.zeroDR)
    (ρ : BoundaryLifts b F RF.TC) :
    {x : {pr : BoundaryLifts b F RF.TC × ContinuousMonoidHom Γ RF.YB //
        (∀ γ : Γ, RF.piBC (pr.2 γ) = pr.1.1.1 γ) ∧ IsBoundaryLift b F RF.TB pr.2 ∧
          ∃ g : ContinuousMonoidHom Γ (RF.scalarCover l h).cover,
            ∀ γ : Γ, (RF.scalarCover l h).p (g γ) = pr.2 γ} // x.1.1 = ρ}
      ≃ CentralOver RF b F l h ρ where
  toFun x :=
    ⟨⟨x.1.1.2, fun γ => by rw [x.1.2.1 γ, x.2]⟩, x.1.2.2.2⟩
  invFun m :=
    ⟨⟨⟨ρ, m.1.1⟩, fun γ => m.1.2 γ,
        RF.isBoundaryLift_of_over b F m.1.1 ρ m.1.2, m.2⟩, rfl⟩
  left_inv x := by
    obtain ⟨⟨⟨ρ', m⟩, hcompat, hbd, hg⟩, rfl⟩ := x
    rfl
  right_inv m := rfl

omit [TopologicalSpace Y] [DiscreteTopology Y] in
/-- **The (139) half count** (the Prop. 8.9 assembly): `2·zBC = |M_B|²·e_Γ(C)` when the radical edge is
nonzero.  Source-generic: the two per-source inputs enter as hypotheses —

* `hlem86` = the source's **Lemma 8.6** half-torsor count (`lemma_8_6_local`/`gammaA` after
  the `CentralOver ρ ↔ MLifts.Central` transport), and
* `hMcount` = the **`2^{2·dim M}` `M`-lift count** over each lower map (props 5.15/5.16).

The bridge fibres `zBC` over the lower exact-image map `ρ` and sums; d6 discharges `hlem86`
and `hMcount` per source. -/
theorem half139_of [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    (hfg : ∃ s : Finset Γ, (Subgroup.closure (s : Set Γ)).topologicalClosure = ⊤)
    (l : RF.DR) (h : l ≠ RF.zeroDR)
    (hlem86 : ∀ ρ : BoundaryLifts b F RF.TC,
      2 * Nat.card (CentralOver RF b F l h ρ) = Nat.card (LiftsOver RF b F ρ))
    (hMcount : ∀ ρ : BoundaryLifts b F RF.TC,
      Nat.card (LiftsOver RF b F ρ) = (Nat.card ↥RF.MB) ^ 2) :
    2 * RF.zBC b F l h = (Nat.card ↥RF.MB) ^ 2 * exactImageCount b F RF.TC := by
  classical
  haveI : Finite (ContinuousMonoidHom Γ RF.YB) := finite_continuousMonoidHom hfg RF.YB
  haveI : Finite (BoundaryLifts b F RF.TC) := finite_boundaryLifts b F RF.TC hfg
  haveI : Fintype (BoundaryLifts b F RF.TC) := Fintype.ofFinite _
  haveI : Finite (BoundaryLifts b F RF.TC × ContinuousMonoidHom Γ RF.YB) := inferInstance
  -- fibration of `zBC` over the `C`-image `ρ`
  have hfib : RF.zBC b F l h
      = ∑ ρ : BoundaryLifts b F RF.TC, Nat.card (CentralOver RF b F l h ρ) := by
    rw [zBC]
    haveI : Finite {pr : BoundaryLifts b F RF.TC × ContinuousMonoidHom Γ RF.YB //
        (∀ γ : Γ, RF.piBC (pr.2 γ) = pr.1.1.1 γ) ∧ IsBoundaryLift b F RF.TB pr.2 ∧
          ∃ g : ContinuousMonoidHom Γ (RF.scalarCover l h).cover,
            ∀ γ : Γ, (RF.scalarCover l h).p (g γ) = pr.2 γ} := Subtype.finite
    rw [Nat.card_congr (Equiv.sigmaFiberEquiv (fun x => x.1.1)).symm, Nat.card_sigma]
    exact Finset.sum_congr rfl (fun ρ _ => Nat.card_congr (zBCfibreEquiv RF b F l h ρ))
  calc 2 * RF.zBC b F l h
      = ∑ ρ : BoundaryLifts b F RF.TC, 2 * Nat.card (CentralOver RF b F l h ρ) := by
        rw [hfib, Finset.mul_sum]
    _ = ∑ ρ : BoundaryLifts b F RF.TC, Nat.card (LiftsOver RF b F ρ) :=
        Finset.sum_congr rfl (fun ρ _ => hlem86 ρ)
    _ = ∑ _ρ : BoundaryLifts b F RF.TC, (Nat.card ↥RF.MB) ^ 2 :=
        Finset.sum_congr rfl (fun ρ _ => hMcount ρ)
    _ = (Nat.card ↥RF.MB) ^ 2 * exactImageCount b F RF.TC := by
        simp only [Finset.sum_const, Finset.card_univ, smul_eq_mul, exactImageCount,
          Nat.card_eq_fintype_card]
        ring

/-! ### The `MLifts` transport

`LiftsOver ρ` and `CentralOver ρ` (bridge vocabulary, over `π_{BC}`) are the central-obstruction framework `MLifts`
and their central relation for the datum `E.radData l h`, over the transported lower map
`ρ' := piBCiso⁻¹ ∘ ρ`.  These equivalences let d6 discharge `half139_of`'s `hlem86`/`hMcount`
directly from the source's `lemma_8_6` and the 5.15/5.16 `M`-lift count. -/

/-- `piBCiso.symm : C → B/M` as a continuous hom (finite discrete ⟹ continuous). -/
noncomputable def piBCisoSymm (D : RadicalCoverData RF.YB) (hD : D.M = RF.MB) :
    ContinuousMonoidHom RF.YC (RF.YB ⧸ D.M) where
  toMonoidHom := (RF.piBCiso D hD).symm.toMonoidHom
  continuous_toFun := continuous_of_discreteTopology

/-- The transport `ρ' := piBCiso⁻¹ ∘ ρ` of a `C`-exact-image map to a `B/M`-valued lower map. -/
noncomputable def rhoPrime (D : RadicalCoverData RF.YB) (hD : D.M = RF.MB)
    (ρ : BoundaryLifts b F RF.TC) : ContinuousMonoidHom Γ (RF.YB ⧸ D.M) :=
  (RF.piBCisoSymm D hD).comp ρ.1.1

omit [TopologicalSpace Y] [DiscreteTopology Y] [IsTopologicalGroup Γ] in
theorem rhoPrime_apply (D : RadicalCoverData RF.YB) (hD : D.M = RF.MB)
    (ρ : BoundaryLifts b F RF.TC) (γ : Γ) :
    RF.rhoPrime b F D hD ρ γ = (RF.piBCiso D hD).symm (ρ.1.1 γ) := rfl

/-- **The `LiftsOver ↔ MLifts` bridge**: `B`-lifts over `ρ` are the unrestricted `M`-lifts of
the transported lower map `ρ'` (`ker π_{BC} = M_B`).  Stated for any `RadicalCoverData` `D`
with `D.M = M_B` (d6 uses `D := E.radData l h`, `hD := rfl`). -/
def liftsOver_equiv (D : RadicalCoverData RF.YB) (hD : D.M = RF.MB)
    (ρ : BoundaryLifts b F RF.TC) :
    LiftsOver RF b F ρ ≃ MLifts D (RF.rhoPrime b F D hD ρ) :=
  Equiv.subtypeEquivRight fun m => by
    refine ⟨fun hover γ => ?_, fun hmk γ => ?_⟩
    · show QuotientGroup.mk (m γ) = (RF.piBCiso D hD).symm (ρ.1.1 γ)
      rw [← hover γ, ← RF.piBCiso_mk D hD, MulEquiv.symm_apply_apply]
    · rw [← RF.piBCiso_mk D hD (m γ), hmk γ, rhoPrime_apply, MulEquiv.apply_symm_apply]

/-- **The `CentralOver ↔ central `MLifts`** bridge**: the `λ`-compatible lifts over `ρ` are the
central `M`-lifts of `ρ'` (the scalar cover of `D`).  With `D := E.radData l h` the scalar
cover is `RF.scalarCover l h`, so the predicates match on the nose. -/
def centralOver_equiv (l : RF.DR) (h : l ≠ RF.zeroDR) (D : RadicalCoverData RF.YB)
    (hD : D.M = RF.MB) (hC : D.C = RF.scalarCover l h) (ρ : BoundaryLifts b F RF.TC) :
    CentralOver RF b F l h ρ ≃ {f : MLifts D (RF.rhoPrime b F D hD ρ) // f.Central} :=
  Equiv.subtypeEquiv (RF.liftsOver_equiv b F D hD ρ) fun m => by
    rw [← hC]; exact Iff.rfl

end RecursionFrame

end SectionEight

end GQ2

/-! ### Paper-tag ledger (auto-generated by paperforge; do not edit)

  * Lemma 8.6 = ⟦lem-radicaledge⟧
-/
