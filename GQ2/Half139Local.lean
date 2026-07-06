import GQ2.RecursionSplice

/-!
# P-16d6d: the (139) half count for the local source `G_ℚ₂`

Discharge the two per-source hypotheses of `half139_via_radData` (`RecursionSplice.lean`) for the
**local** source `Γ = G_ℚ₂ = AbsGalQ2`, producing the (139) identity
`2·zBC = |M_B|²·exactImageCount` in exactly the shape of the `RecursionInputs.half139` field
(consumed at P-16d6e).

Two obligations, per boundary lift `ρ` of the `C`-target:

* **`hlem86M`** — the source's Lemma 8.6 half-torsor count
  `2·#{central M-lifts} = #(M-lifts)`.  This is `lemma_8_6_local` (✓, B6/B7) applied to the
  transported lower map `ρ' = rhoPrime … ρ`, with `hedge` threaded from the `NoDescent` field
  hypothesis and `hρ'` from `rhoPrime_surjective` (below).  ~Pure plumbing.
* **`hMcountM`** — the unrestricted `M`-lift count `#(M-lifts) = |M_B|²`.  The genuine content:
  `MLifts` is a `Z¹_cont(G_ℚ₂, M_B)`-torsor and `#Z¹ = |M_B|²·#H²(G_ℚ₂, M_B)`
  (`card_Z1_eq`), so the identity reduces to `#H²(G_ℚ₂, M_B) = 1`, i.e. the vanishing of the
  `YC`-coinvariants of `M_B`.

Axioms (audit at close): `⊆ {B6, B7, B9}` — B6/B7 via `lemma_8_6_local` and the local Euler
characteristic behind `card_Z1_eq`.
-/

namespace GQ2

namespace SectionEight

open CentralObstruction AffineTLift ContCoh LocalLiftingDuality FoxH

variable {H E : Type} [Group H] [TopologicalSpace H] [DiscreteTopology H] [Finite H]
  [CommGroup E] [TopologicalSpace E] [DiscreteTopology E] [Finite E]
variable {Y : Type} [Group Y] [TopologicalSpace Y] [DiscreteTopology Y] [Finite Y]
variable {T : MarkedTarget H E Y} {Blk : SectionSeven.MinimalBlock T.LY}

/-! ## `rhoPrime` surjectivity (both sources) -/

/-- **The transported lower map `ρ' = piBCiso⁻¹ ∘ ρ` is surjective.**  A boundary lift `ρ` wraps a
`ContSurj` (`ρ.1.2 : Surjective ρ.1.1`), and `piBCiso.symm` is a `MulEquiv`, so the composite is
onto `B/M`.  Feeds `lemma_8_6_local`'s surjectivity hypothesis. -/
theorem rhoPrime_surjective {Γ : Type} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    (RF : RecursionFrame T Blk) (b : ContinuousMonoidHom Γ ↥boundarySubgroup) (F : BoundaryFrame H E)
    (D : RadicalCoverData RF.YB) (hD : D.M = RF.MB) (ρ : BoundaryLifts b F RF.TC) :
    Function.Surjective (RF.rhoPrime b F D hD ρ) := fun y => by
  obtain ⟨γ, hγ⟩ := ρ.1.2 (RF.piBCiso D hD y)
  exact ⟨γ, by rw [RF.rhoPrime_apply, hγ, MulEquiv.symm_apply_apply]⟩

/-! ## The `M`-layer additive module (for the `Z¹` count)

`↥D.M` is elementary abelian (`D.helem`), so `Additive ↥D.M` is a finite `𝔽₂`-space; conjugation
by any coset rep of `Bg/D.M` is well-defined (`D` abelian ⟹ rep-independent) and gives the
`Bg/D.M`-action, pulled back through a lower map `ρ` to a `G_ℚ₂`-action.  These two helpers are the
`D.M`-analogues of `RadicalEdgeLocal`'s `D.T` versions. -/

/-- Conjugation of `M`-elements only depends on the `M`-coset of the conjugator (`M` abelian). -/
private theorem conj_eq_of_mk_eq_M {Bg : Type} [Group Bg] [Finite Bg] {D : RadicalCoverData Bg}
    {b b' : Bg} (h : (QuotientGroup.mk b : Bg ⧸ D.M) = QuotientGroup.mk b') (m : ↥D.M) :
    b * m.1 * b⁻¹ = b' * m.1 * b'⁻¹ := by
  have hm : b⁻¹ * b' ∈ D.M := (QuotientGroup.eq (s := D.M)).mp h
  have hcomm := D.hcomm _ hm _ m.2
  calc b * m.1 * b⁻¹
      = b * (m.1 * (b⁻¹ * b') * (b⁻¹ * b')⁻¹) * b⁻¹ := by group
    _ = b * ((b⁻¹ * b') * m.1 * (b⁻¹ * b')⁻¹) * b⁻¹ := by rw [← hcomm]
    _ = b' * m.1 * b'⁻¹ := by group

/-- The commutative group structure on `↥M` (`M` abelian, `D.hcomm`). -/
@[reducible] private def mCommGroup {Bg : Type} [Group Bg] [Finite Bg]
    (D : RadicalCoverData Bg) : CommGroup ↥D.M :=
  { (inferInstance : Group ↥D.M) with
    mul_comm := fun a b => Subtype.ext (D.hcomm _ a.2 _ b.2) }

/-! ## The two hypotheses for `G_ℚ₂` -/

/-- **`hlem86M` for `G_ℚ₂`** — the source's Lemma 8.6 half-torsor count over every boundary lift,
for the radical datum `En.radData l h`, threading the `NoDescent` field hypothesis. -/
theorem hlem86M_local [CompactSpace AbsGalQ2] [TotallyDisconnectedSpace AbsGalQ2]
    [IsTopologicalGroup AbsGalQ2]
    (RF : RecursionFrame T Blk) (b : ContinuousMonoidHom AbsGalQ2 ↥boundarySubgroup)
    (F : BoundaryFrame H E) (En : RF.Enrichment)
    (hfg : ∃ s : Finset AbsGalQ2, (Subgroup.closure (s : Set AbsGalQ2)).topologicalClosure = ⊤)
    (l : RF.DR) (h : l ≠ RF.zeroDR)
    (hedge : ¬∃ N : Subgroup (RF.scalarCover l h).cover, N.Normal ∧
      N.map (RF.scalarCover l h).p = RF.TBsub ∧ (RF.scalarCover l h).z ∉ N)
    (ρ : BoundaryLifts b F RF.TC) :
    2 * Nat.card {f : MLifts (En.radData l h) (RF.rhoPrime b F (En.radData l h) rfl ρ) // f.Central}
      = Nat.card (MLifts (En.radData l h) (RF.rhoPrime b F (En.radData l h) rfl ρ)) :=
  lemma_8_6_local (En.radData l h) hfg hedge (RF.rhoPrime b F (En.radData l h) rfl ρ)
    (rhoPrime_surjective RF b F (En.radData l h) rfl ρ)

/-- **`hMcountM` for `G_ℚ₂`** — the unrestricted `M`-lift count `#(M-lifts) = |M_B|²`.

**PARTIALLY PROVED.**  Steps 1 + 3 below (the additive `M`-module with the `ρ'`-conjugation
action + `card_Z1_eq`) are now realized inline: `key : #Z¹ = |M_B|²·#fixedPts` holds.  Two scoped
`sorry`s remain — `hfix` (Step 4, `#fixedPts = 1`, ⟵ the proved `lemma_7_1_dual`, just a bridge)
and `htorsor` (Step 2, the `Z¹`-torsor bridge + nonemptiness).  This fact (`κ_M = #MLifts`,
ρ-independent) is also the shared deep input consumed by the concurrent P-16d6b
(`PhaseMuIndep.tcocycle_mu_indep`'s `hML`/`κM`).  Full roadmap in `docs/p16d6d-hMcount-handoff.md`;
the route (all steps over `G_ℚ₂ = AbsGalQ2`):

1. **Additive `M`-module** `MBmod := Additive ↥(En.radData l h).M` (`= Additive ↥RF.MB`), with the
   `ρ'`-conjugation `DistribMulAction AbsGalQ2 MBmod` and the descended `DistribMulAction RF.YC
   MBmod` (factoring through `ρ'`, `hcomp`), continuity, `2`-torsion (`RF.MB_elem`).  **Pattern:
   copy `RadicalEdgeLocal.lean:73–135`** (the `D.T` version) with `D.T ⤳ D.M`, using `D.hM`
   (normality ⟹ conjugation stays in `M`) and `D.hcomm` (`M` abelian ⟹ the action factors through
   `Bg/M`), which are the exact `D.T`-analogues already invoked there.
2. **Torsor bridge** `MLifts D ρ' ≃ Z¹_cont(AbsGalQ2, MBmod)` — `f ↦ (γ ↦ f γ · f₀ γ⁻¹)` for a base
   lift `f₀`.  **Nonemptiness of `MLifts` is a theorem, not a hypothesis**: the lift obstruction of
   `ρ' : Γ → YB/M_B` through `YB ↠ YB/M_B` lives in `H²(AbsGalQ2, M_B)`, which is `0` by step 4 —
   so `MLifts` is nonempty and the torsor bijection holds.  (No existing `H²`-obstruction-vanishing
   lemma in-repo; this is the piece to build/locate.)
3. **`card_Z1_eq`** (`LocalLiftingDuality.lean:264`, B7 Euler char):
   `#Z¹(AbsGalQ2, MBmod) = |MBmod|² · #fixedPts RF.YC (ElemDual MBmod)`, feeding `hρ = rhoPrime`
   surjectivity (`rhoPrime_surjective`), `hcomp` from step 1, `hA₂` from `RF.MB_elem`.
4. **`#fixedPts RF.YC (ElemDual MBmod) = 1`** — i.e. `H²(AbsGalQ2, M_B) = 0`
   (`card_H2_eq_fixedPts`, B6), i.e. `(M_B^∨)^{YC} = 0`.  **The group theory is already proved:**
   this is `GQ2.SectionSeven.lemma_7_1_dual` (`SectionSeven.lean:449`, std-3, no sorry) — "`K` has no
   `Y`-normal subgroup of index 2 above `R`" = `(M^∨)^C = 0`, via minimality of `K` + the `V = P/S`
   chief dichotomy.  Only a bridge (a nonzero `YC`-invariant functional's kernel ↦ an index-2
   `Y`-normal `X` with `Blk.R ≤ X ≤ Blk.K`, refuted by `lemma_7_1_dual`) remains — no new math.
5. Combine: `#MLifts = #Z¹ = |M_B|² · 1 = |M_B|²`.

Expected axioms at close: `std-3 + B6 + B7` (B6 via `card_H2_eq_fixedPts`, B7 via `card_Z1_eq`). -/
theorem hMcountM_local [CompactSpace AbsGalQ2] [TotallyDisconnectedSpace AbsGalQ2]
    [IsTopologicalGroup AbsGalQ2]
    (RF : RecursionFrame T Blk) (b : ContinuousMonoidHom AbsGalQ2 ↥boundarySubgroup)
    (F : BoundaryFrame H E) (En : RF.Enrichment)
    (hfg : ∃ s : Finset AbsGalQ2, (Subgroup.closure (s : Set AbsGalQ2)).topologicalClosure = ⊤)
    (l : RF.DR) (h : l ≠ RF.zeroDR) (ρ : BoundaryLifts b F RF.TC) :
    Nat.card (MLifts (En.radData l h) (RF.rhoPrime b F (En.radData l h) rfl ρ))
      = (Nat.card ↥RF.MB) ^ 2 := by
  classical
  have hρ's : Function.Surjective (RF.rhoPrime b F (En.radData l h) rfl ρ) :=
    rhoPrime_surjective RF b F (En.radData l h) rfl ρ
  -- `M_B = (En.radData l h).M = RF.MB` as an additive 𝔽₂-space with the `ρ'`-conjugation action
  letI : CommGroup ↥(En.radData l h).M := mCommGroup (En.radData l h)
  letI : TopologicalSpace (Additive ↥(En.radData l h).M) :=
    (inferInstance : TopologicalSpace ↥(En.radData l h).M)
  haveI : DiscreteTopology (Additive ↥(En.radData l h).M) :=
    ⟨(inferInstance : DiscreteTopology ↥(En.radData l h).M).eq_bot⟩
  haveI : Finite (Additive ↥(En.radData l h).M) := (inferInstance : Finite ↥(En.radData l h).M)
  letI actC : DistribMulAction (RF.YB ⧸ (En.radData l h).M) (Additive ↥(En.radData l h).M) :=
    { smul := fun c m => Additive.ofMul
        ⟨Quotient.out c * (Additive.toMul m).1 * (Quotient.out c)⁻¹,
          (En.radData l h).hM.conj_mem _ (Additive.toMul m).2 _⟩
      one_smul := fun m => by
        apply Additive.toMul.injective; apply Subtype.ext
        show Quotient.out (1 : RF.YB ⧸ (En.radData l h).M) * (Additive.toMul m).1
            * (Quotient.out (1 : RF.YB ⧸ (En.radData l h).M))⁻¹ = (Additive.toMul m).1
        have h1 : (Quotient.out (1 : RF.YB ⧸ (En.radData l h).M)) ∈ (En.radData l h).M := by
          have := QuotientGroup.out_eq' (1 : RF.YB ⧸ (En.radData l h).M)
          rwa [QuotientGroup.eq_one_iff] at this
        rw [(En.radData l h).hcomm _ h1 _ (Additive.toMul m).2]; group
      mul_smul := fun c c' m => by
        apply Additive.toMul.injective; apply Subtype.ext
        show Quotient.out (c * c') * (Additive.toMul m).1 * (Quotient.out (c * c'))⁻¹
          = Quotient.out c * (Quotient.out c' * (Additive.toMul m).1 * (Quotient.out c')⁻¹)
              * (Quotient.out c)⁻¹
        rw [show Quotient.out c * (Quotient.out c' * (Additive.toMul m).1 * (Quotient.out c')⁻¹)
              * (Quotient.out c)⁻¹
            = (Quotient.out c * Quotient.out c') * (Additive.toMul m).1
              * (Quotient.out c * Quotient.out c')⁻¹ from by group]
        exact conj_eq_of_mk_eq_M (by rw [QuotientGroup.out_eq', QuotientGroup.mk_mul,
          QuotientGroup.out_eq', QuotientGroup.out_eq']) (Additive.toMul m)
      smul_zero := fun c => by
        apply Additive.toMul.injective; apply Subtype.ext
        show Quotient.out c * (1 : RF.YB) * (Quotient.out c)⁻¹ = 1
        group
      smul_add := fun c m m' => by
        apply Additive.toMul.injective; apply Subtype.ext
        show Quotient.out c * ((Additive.toMul m).1 * (Additive.toMul m').1) * (Quotient.out c)⁻¹
          = (Quotient.out c * (Additive.toMul m).1 * (Quotient.out c)⁻¹)
              * (Quotient.out c * (Additive.toMul m').1 * (Quotient.out c)⁻¹)
        group }
  letI actG : DistribMulAction AbsGalQ2 (Additive ↥(En.radData l h).M) :=
    DistribMulAction.compHom (Additive ↥(En.radData l h).M)
      (RF.rhoPrime b F (En.radData l h) rfl ρ).toMonoidHom
  have hcomp : ∀ (γ : AbsGalQ2) (a : Additive ↥(En.radData l h).M),
      γ • a = (RF.rhoPrime b F (En.radData l h) rfl ρ) γ • a := fun _ _ => rfl
  haveI : ContinuousSMul AbsGalQ2 (Additive ↥(En.radData l h).M) := by
    constructor
    have hfac : (fun p : AbsGalQ2 × Additive ↥(En.radData l h).M => p.1 • p.2)
        = (fun cq : (RF.YB ⧸ (En.radData l h).M) × ↥(En.radData l h).M =>
            Additive.ofMul (⟨Quotient.out cq.1 * cq.2.1 * (Quotient.out cq.1)⁻¹,
              (En.radData l h).hM.conj_mem _ cq.2.2 _⟩ : ↥(En.radData l h).M))
          ∘ (fun p : AbsGalQ2 × Additive ↥(En.radData l h).M =>
              ((RF.rhoPrime b F (En.radData l h) rfl ρ p.1 : RF.YB ⧸ (En.radData l h).M),
                Additive.toMul p.2)) := by
      funext p; rfl
    rw [hfac]
    exact continuous_of_discreteTopology.comp
      (((RF.rhoPrime b F (En.radData l h) rfl ρ).continuous_toFun.comp continuous_fst).prodMk
        continuous_snd)
  have hA₂ : ∀ a : Additive ↥(En.radData l h).M, a + a = 0 := fun a => by
    apply Additive.toMul.injective
    show (Additive.toMul a) * (Additive.toMul a) = 1
    exact Subtype.ext ((En.radData l h).helem _ (Additive.toMul a).2)
  -- Step 3: `#Z¹ = |M_B|² · #fixedPts` (`card_Z1_eq`, B7 Euler char)
  have key := card_Z1_eq hρ's hcomp hA₂
  -- Step 4: `#fixedPts = 1`  ⟵  `lemma_7_1_dual` (the `(M^∨)^C = 0` group theory, std-3)
  have hfix : Nat.card (fixedPts (RF.YB ⧸ (En.radData l h).M)
      (ElemDual (Additive ↥(En.radData l h).M))) = 1 := by
    sorry
  -- Step 2: the `Z¹`-torsor bridge (`MLifts` nonempty from `#H² = 1`, then `≃ Z¹`)
  have htorsor : Nat.card (MLifts (En.radData l h) (RF.rhoPrime b F (En.radData l h) rfl ρ))
      = Nat.card (Z1 AbsGalQ2 (Additive ↥(En.radData l h).M)) := by
    sorry
  rw [htorsor, key, hfix, mul_one]
  rfl

/-- **P-16d6d deliverable**: the (139) half count for `G_ℚ₂`, in the exact shape of the
`RecursionInputs.half139` field (consumed at P-16d6e). -/
theorem half139_local [CompactSpace AbsGalQ2] [TotallyDisconnectedSpace AbsGalQ2]
    [IsTopologicalGroup AbsGalQ2]
    (RF : RecursionFrame T Blk) (b : ContinuousMonoidHom AbsGalQ2 ↥boundarySubgroup)
    (F : BoundaryFrame H E) (En : RF.Enrichment)
    (hfg : ∃ s : Finset AbsGalQ2, (Subgroup.closure (s : Set AbsGalQ2)).topologicalClosure = ⊤)
    (l : RF.DR) (h : l ≠ RF.zeroDR)
    (hedge : ¬∃ N : Subgroup (RF.scalarCover l h).cover, N.Normal ∧
      N.map (RF.scalarCover l h).p = RF.TBsub ∧ (RF.scalarCover l h).z ∉ N) :
    2 * RF.zBC b F l h = (Nat.card ↥RF.MB) ^ 2 * exactImageCount b F RF.TC :=
  half139_via_radData RF b F En l h hfg
    (hlem86M_local RF b F En hfg l h hedge) (hMcountM_local RF b F En hfg l h)

end SectionEight

end GQ2
