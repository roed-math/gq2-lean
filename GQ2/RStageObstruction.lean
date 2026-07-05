import GQ2.SectionEight

/-!
# §8 R-stage obstruction module — the reduction  (P-16d2)

`GQ2.SectionEight.stageR136_of` (P-16d item 1, combinatorial core) derives the (136) display of
Prop 8.9 from an obstruction-module datum stated in `Module.Dual`-of-`W` vocabulary
(`W`, `o : BoundaryLifts(B) → W`, `e : D_R ≃ Wᵛ`, `hmB`/`hobs`/`hfib`).  This file repackages
that datum in the **natural obstruction shape**: the obstruction of a `B`-stage boundary lift is
a **linear functional on the scalar-character space** `D_R`,

  `obs : BoundaryLifts(B) → D_Rᵛ`,   `obs g λ = ` the `λ`-scalar obstruction of `g` (in `𝔽₂`),

so that

* `obs g λ = 0 ⟺ g` lifts through the `λ`-cover `p_λ`  (the `m_{Γ,λ}(B)` count, `hmB`),
* `obs g = 0 ⟺ g` lifts all the way to `Y`  (`hobs`), and
* every liftable fibre has the torsor size `z_R`  (`hfib`, the 5.15/5.16 `Z¹`-numeric).

`stageR136_ofObstruction` takes exactly this data (with a chosen `𝔽₂`-module realization
`D_Rmod ≃ D_R` of the scalar-character index — `RecursionFrame.DR` is a bare `Fintype`, so the
linear structure is supplied here) and produces the (136) conclusion, by taking `W := D_Rmodᵛ`
and `e := evalEquiv ∘ (·⁻¹)` the finite-dimensional double-dual identification.  All std-3; no
axioms — the arithmetic axioms (B6, B7) enter only when a *caller* discharges `hfib` from the
numerics.

## Design status (P-16d2, 2026-07-05)

This is the **reduction half** of P-16d2, and is complete and reusable.  Constructing the
`obs`/`hmB`/`hobs`/`hfib` witness for the concrete `𝒴`-frame needs one input the **bare
`RecursionFrame` + `Enrichment` do not carry**: the compatibility that the abstract per-`λ`
`scalarCover l` really is the `λ`-pushout `Y/ker λ ↠ Y/R` of the *single* radical extension
`Y ↠ B` (the frame stores `scalarCover` as unrelated central covers, documented — not enforced —
as the pushouts).  Without that link, `λ ↦ [g lifts through p_λ]` has no reason to be `𝔽₂`-linear
(the `obs`-linearity) and "lifts through every `p_λ` ⟺ lifts to `Y`" (the `hobs` separation) is
not derivable.  This is a **design escalation**, analysed with the full construction route in
[`docs/p16d2-plan.md`](../docs/p16d2-plan.md): either extend the frame with the pushout-compatible
map family `Y ↠ (scalarCover l).cover`, or state the witness for the concrete `𝒴`-frame (P-16d5/d6)
where the covers are the pushouts by construction.  Either way the witness feeds *this* lemma.
-/

namespace GQ2

namespace SectionEight

open SectionSeven

variable {H E : Type} [Group H] [TopologicalSpace H] [DiscreteTopology H] [Finite H]
  [CommGroup E] [TopologicalSpace E] [DiscreteTopology E] [Finite E]
variable {Y : Type} [Group Y] [TopologicalSpace Y] [DiscreteTopology Y] [Finite Y]
variable {Γ : Type} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
  [CompactSpace Γ] [TotallyDisconnectedSpace Γ]

/-- **The R-stage obstruction module → (136)** (P-16d2 reduction).  Given a finite `𝔽₂`-module
`D_Rmod` realizing the scalar-character index `D_R` (`toDR`, sending `0 ↦ zeroDR`) and the
obstruction as a linear functional `obs g ∈ D_Rmodᵛ` on each `B`-stage boundary lift, whose

* `λ`-vanishing `obs g λ = 0` counts the `λ`-cover-liftable maps `m_{Γ,λ}(B)` (`hmB`),
* total vanishing `obs g = 0` detects liftability to `Y` (`hobs`), and
* liftable fibres have the constant torsor size `z_R` (`hfib`),

the (136) display holds.  Proof: take `W := D_Rmodᵛ`, `o := obs`, and identify
`e : D_R ≃ Wᵛ = D_Rmodᵛᵛ` by the finite-dimensional double-dual `evalEquiv`, then apply
`stageR136_of`. -/
theorem stageR136_ofObstruction
    {T : MarkedTarget H E Y} {Blk : SectionSeven.MinimalBlock T.LY}
    (RF : RecursionFrame T Blk)
    (hfg : ∃ s : Finset Γ, (Subgroup.closure (s : Set Γ)).topologicalClosure = ⊤)
    (b : ContinuousMonoidHom Γ ↥boundarySubgroup) (F : BoundaryFrame H E)
    (DRmod : Type) [AddCommGroup DRmod] [Module (ZMod 2) DRmod] [Finite DRmod]
    (toDR : DRmod ≃ RF.DR) (h0 : toDR.symm RF.zeroDR = 0)
    (obs : BoundaryLifts b F RF.TB → Module.Dual (ZMod 2) DRmod)
    (hmB : ∀ (l : RF.DR), l ≠ RF.zeroDR →
      RF.mB b F l = Nat.card {g : BoundaryLifts b F RF.TB // obs g (toDR.symm l) = 0})
    (hobs : ∀ g : BoundaryLifts b F RF.TB,
      obs g = 0 ↔ ∃ f : BoundaryLifts b F T, RF.liftB b F f = g)
    (hfib : ∀ g : BoundaryLifts b F RF.TB, obs g = 0 →
      Nat.card {f : BoundaryLifts b F T // RF.liftB b F f = g} = RF.zR) :
    (Nat.card RF.DR : ℤ) * exactImageCount b F T
      = RF.zR * ∑ᶠ l : RF.DR,
          (2 * (RF.mB b F l : ℤ) - exactImageCount b F RF.TB) := by
  classical
  -- `W := D_Rmodᵛ`; identify `D_R ≃ Wᵛ = D_Rmodᵛᵛ` by the double-dual evaluation.
  set e : RF.DR ≃ Module.Dual (ZMod 2) (Module.Dual (ZMod 2) DRmod) :=
    toDR.symm.trans (Module.evalEquiv (ZMod 2) DRmod).toEquiv with he_def
  -- evaluation identity: `e l φ = φ (toDR.symm l)`.
  have heval : ∀ (l : RF.DR) (φ : Module.Dual (ZMod 2) DRmod),
      e l φ = φ (toDR.symm l) := by
    intro l φ
    simp [he_def, Equiv.trans_apply, Module.evalEquiv_apply, Module.Dual.eval_apply]
  have he0 : e RF.zeroDR = 0 := by
    have : e RF.zeroDR (0 : Module.Dual (ZMod 2) DRmod) = 0 := by
      rw [heval]; simp
    ext φ
    rw [heval, h0]; simp
  refine stageR136_of RF hfg b F (Module.Dual (ZMod 2) DRmod) obs e he0 ?_ hobs hfib
  intro l hl
  rw [hmB l hl]
  exact Nat.card_congr (Equiv.subtypeEquivRight fun g => by rw [heval l (obs g)])

end SectionEight

end GQ2
