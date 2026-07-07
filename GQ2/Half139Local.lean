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

/-! ## The `(M∨)^C = 0` refutation (Lemma 7.1 / simple-head duality) -/

/-- **No nonzero conjugation-invariant `M`-character** (`(M_B^∨)^{Y} = 0`, the operational form of
Lemma 7.1 / `Hom_C(M, 𝔽₂) = 0`): any additive `ψ : ↥M_B → 𝔽₂` invariant under `Y`-conjugation is
identically zero.  A nonzero such `ψ` would pull back (through `s : Blk.K ↠ M_B`, `s = piB|_K`) to a
surjective character `φ : Blk.K ↠ 𝔽₂` whose kernel maps to a `Y`-normal index-2 subgroup `X` with
`Blk.R ≤ X ≤ Blk.K`, contradicting `SectionSeven.lemma_7_1_dual`.  This is the shared kernel of both
`hMcountM_local` (there via the `fixedPts (ElemDual …)` packaging) and P-16d6e3's `hpartial_local`
(the nondegeneracy residue). -/
theorem mchar_conj_invariant_eq_zero (RF : RecursionFrame T Blk)
    (En : RF.Enrichment) (l : RF.DR) (h : l ≠ RF.zeroDR)
    (ψ : ↥(En.radData l h).M → ZMod 2)
    (hadd : ∀ m m' : ↥(En.radData l h).M, ψ (m * m') = ψ m + ψ m')
    (hconj : ∀ (bb : RF.YB) (m : ↥(En.radData l h).M)
        (hm : bb * (m : RF.YB) * bb⁻¹ ∈ (En.radData l h).M),
      ψ ⟨bb * (m : RF.YB) * bb⁻¹, hm⟩ = ψ m) :
    ∀ m : ↥(En.radData l h).M, ψ m = 0 := by
  by_contra hcon
  rw [not_forall] at hcon
  obtain ⟨m₀, hm₀⟩ := hcon
  have hψ1 : ψ 1 = 0 := by
    have h := hadd 1 1; rw [mul_one] at h
    nth_rewrite 1 [← add_zero (ψ 1)] at h
    exact (add_left_cancel h).symm
  have hmem : ∀ k : ↥Blk.K, RF.piB k.1 ∈ (En.radData l h).M := by
    intro k
    show RF.piB k.1 ∈ RF.MB
    rw [RF.MB_eq]; exact Subgroup.mem_map.mpr ⟨k.1, k.2, rfl⟩
  -- `s : Blk.K ↠ M_B` and the character `φ = ψ ∘ s : Blk.K →* μ₂`
  let s : ↥Blk.K →* ↥(En.radData l h).M :=
    (RF.piB.comp Blk.K.subtype).codRestrict (En.radData l h).M (fun k => hmem k)
  have hs : ∀ k : ↥Blk.K, (s k).1 = RF.piB k.1 := fun _ => rfl
  have hs_surj : Function.Surjective s := by
    intro m
    obtain ⟨k, hk, hkeq⟩ := (RF.MB_eq ▸ m.2 : m.1 ∈ Blk.K.map RF.piB)
    exact ⟨⟨k, hk⟩, Subtype.ext hkeq⟩
  let φ : ↥Blk.K →* Multiplicative (ZMod 2) :=
    { toFun := fun k => Multiplicative.ofAdd (ψ (s k))
      map_one' := by rw [s.map_one, hψ1]; rfl
      map_mul' := fun a b => by simp only [map_mul, hadd]; rfl }
  have hφ_apply : ∀ k, φ k = Multiplicative.ofAdd (ψ (s k)) := fun _ => rfl
  have hφne : φ ≠ 1 := by
    intro hφ1
    obtain ⟨k, hk⟩ := hs_surj m₀
    apply hm₀
    have hk1 : φ k = 1 := by rw [hφ1]; rfl
    have h2 : ψ (s k) = 0 := by
      have := congrArg Multiplicative.toAdd hk1
      simpa [hφ_apply] using this
    rw [hk] at h2
    exact h2
  have hφsurj : Function.Surjective φ := by
    intro y
    rcases eq_or_ne y 1 with rfl | hy
    · exact ⟨1, map_one φ⟩
    · obtain ⟨k, hk⟩ := not_forall.mp (fun hh => hφne (MonoidHom.ext hh))
      refine ⟨k, ?_⟩
      have hpin : ∀ z : Multiplicative (ZMod 2), z ≠ 1 → z = Multiplicative.ofAdd 1 := by decide
      rw [hpin _ hk, hpin _ hy]
  set X : Subgroup Y := φ.ker.map Blk.K.subtype with hXdef
  have hXK : X ≤ Blk.K := by rw [hXdef]; exact Subgroup.map_subtype_le _
  have hRX : Blk.R ≤ X := by
    intro r hr
    have hrK : r ∈ Blk.K := SectionSeven.frattiniLike_le Blk.K hr
    refine Subgroup.mem_map.mpr ⟨⟨r, hrK⟩, ?_, rfl⟩
    rw [MonoidHom.mem_ker, hφ_apply]
    have hs1 : s ⟨r, hrK⟩ = 1 := Subtype.ext (by
      rw [hs]
      show RF.piB r = 1
      exact (RF.ker_piB.symm ▸ hr : r ∈ RF.piB.ker))
    rw [hs1, hψ1]; rfl
  have hXnormal : X.Normal := by
    rw [hXdef]
    refine ⟨fun x hx y => ?_⟩
    obtain ⟨k, hkker, hkeq⟩ := Subgroup.mem_map.mp hx
    have hxK : x ∈ Blk.K := hkeq ▸ k.2
    have hyk : y * x * y⁻¹ ∈ Blk.K := Blk.hK.conj_mem x hxK y
    refine Subgroup.mem_map.mpr ⟨⟨y * x * y⁻¹, hyk⟩, ?_, rfl⟩
    rw [MonoidHom.mem_ker] at hkker ⊢
    rw [hφ_apply] at hkker ⊢
    -- `ψ (s⟨y·x·y⁻¹⟩) = ψ (s⟨x⟩)` via raw conjugation by `piB y`
    have hsconj : s ⟨y * x * y⁻¹, hyk⟩
        = ⟨RF.piB y * (s ⟨x, hxK⟩ : RF.YB) * (RF.piB y)⁻¹,
            (En.radData l h).hM.conj_mem _ (s ⟨x, hxK⟩).2 _⟩ := by
      apply Subtype.ext
      show RF.piB (y * x * y⁻¹) = RF.piB y * (s ⟨x, hxK⟩ : RF.YB) * (RF.piB y)⁻¹
      rw [map_mul, map_mul, map_inv, hs]
    have hcv : ψ (s ⟨y * x * y⁻¹, hyk⟩) = ψ (s ⟨x, hxK⟩) := by
      rw [hsconj]
      exact hconj (RF.piB y) (s ⟨x, hxK⟩) _
    have hkx : s ⟨x, hxK⟩ = s k := congrArg s (Subtype.ext hkeq.symm)
    rw [hcv, hkx]; exact hkker
  have hidx : (X.subgroupOf Blk.K).index = 2 := by
    have hcm : X.subgroupOf Blk.K = φ.ker := by
      rw [hXdef, Subgroup.subgroupOf,
        Subgroup.comap_map_eq_self_of_injective Blk.K.subtype_injective]
    show Nat.card (↥Blk.K ⧸ (X.subgroupOf Blk.K)) = 2
    rw [hcm, Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective φ hφsurj).toEquiv]
    simp
  exact absurd ⟨X, hXnormal, hRX, hXK, hidx⟩ (SectionSeven.lemma_7_1_dual Blk)

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

/-- **`hMcountM` for `G_ℚ₂`** — the unrestricted `M`-lift count `#(M-lifts) = |M_B|²`.  **PROVED.**

Fully proved inline (no sorry): `key : #Z¹ = |M_B|²·#fixedPts` (`card_Z1_eq`), `hfix : #fixedPts = 1`
(the `lemma_7_1_dual` bridge — a nonzero `YC`-invariant functional's kernel gives a `Y`-normal
index-2 `X` with `Blk.R ≤ X ≤ Blk.K`, refuted by `lemma_7_1_dual`), the explicit bijection
`MLifts D ρ' ≃ Z¹_cont(G_ℚ₂, M_B)` (`f ↦ (γ ↦ f γ · f₀ γ⁻¹)`, a `Z¹`-torsor under the ρ'-conjugation
action), and — the previously-open piece — **nonemptiness `Nonempty (MLifts D ρ')`** via the
extension-splitting argument: a continuous set-section `s = Quotient.out ∘ ρ'` gives a factor-set
2-cocycle `c(γ,δ) = s γ · s δ · s(γδ)⁻¹ ∈ Z²(G_ℚ₂, M_B)`, which is a coboundary `c = δ¹ψ` because
`#H²(G_ℚ₂,M_B) = 1` (`card_H2_eq_fixedPts` + `hfix`), and then `f γ = (toMul (ψ γ))⁻¹ · s γ` is a
continuous homomorphic lift of `ρ'`.  This `#MLifts` count is also the shared deep input consumed
by the concurrent P-16d6b (`PhaseMuIndep.tcocycle_mu_indep`'s `hML`/`κM`).  The route
(all steps over `G_ℚ₂ = AbsGalQ2`):

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
    have hzero : ∀ lam : ElemDual (Additive ↥(En.radData l h).M),
        (∀ g : RF.YB ⧸ (En.radData l h).M, g • lam = lam) → lam = 0 := by
      intro lam hlam
      by_contra hlamne
      have hinv : ∀ (c : RF.YB ⧸ (En.radData l h).M) (a : Additive ↥(En.radData l h).M),
          lam (c • a) = lam a := by
        intro c a
        have h2 : (c⁻¹ • lam) a = lam a := by rw [hlam c⁻¹]
        rwa [ElemDual.smul_apply, inv_inv] at h2
      have hmem : ∀ k : ↥Blk.K, RF.piB k.1 ∈ (En.radData l h).M := by
        intro k
        show RF.piB k.1 ∈ RF.MB
        rw [RF.MB_eq]; exact Subgroup.mem_map.mpr ⟨k.1, k.2, rfl⟩
      -- `s : Blk.K ↠ M_B` and the character `φ = lam ∘ s : Blk.K →* μ₂`
      let s : ↥Blk.K →* ↥(En.radData l h).M :=
        (RF.piB.comp Blk.K.subtype).codRestrict (En.radData l h).M (fun k => hmem k)
      have hs : ∀ k : ↥Blk.K, (s k).1 = RF.piB k.1 := fun _ => rfl
      have hs_surj : Function.Surjective s := by
        intro m
        obtain ⟨k, hk, hkeq⟩ := (RF.MB_eq ▸ m.2 : m.1 ∈ Blk.K.map RF.piB)
        exact ⟨⟨k, hk⟩, Subtype.ext hkeq⟩
      let φ : ↥Blk.K →* Multiplicative (ZMod 2) :=
        { toFun := fun k => Multiplicative.ofAdd (lam (Additive.ofMul (s k)))
          map_one' := by simp
          map_mul' := fun a b => by simp [map_mul] }
      have hφ_apply : ∀ k, φ k = Multiplicative.ofAdd (lam (Additive.ofMul (s k))) := fun _ => rfl
      have hφne : φ ≠ 1 := by
        intro hφ1
        apply hlamne
        ext a
        show lam a = 0
        obtain ⟨k, hk⟩ := hs_surj (Additive.toMul a)
        have h0 : lam (Additive.ofMul (s k)) = 0 := by
          have hk1 : φ k = 1 := by rw [hφ1]; rfl
          have := congrArg Multiplicative.toAdd hk1
          simpa [hφ_apply] using this
        rw [hk] at h0
        exact h0
      have hφsurj : Function.Surjective φ := by
        intro y
        rcases eq_or_ne y 1 with rfl | hy
        · exact ⟨1, map_one φ⟩
        · obtain ⟨k, hk⟩ := not_forall.mp (fun hh => hφne (MonoidHom.ext hh))
          refine ⟨k, ?_⟩
          have hpin : ∀ z : Multiplicative (ZMod 2), z ≠ 1 → z = Multiplicative.ofAdd 1 := by decide
          rw [hpin _ hk, hpin _ hy]
      set X : Subgroup Y := φ.ker.map Blk.K.subtype with hXdef
      have hXK : X ≤ Blk.K := by rw [hXdef]; exact Subgroup.map_subtype_le _
      have hRX : Blk.R ≤ X := by
        intro r hr
        have hrK : r ∈ Blk.K := SectionSeven.frattiniLike_le Blk.K hr
        refine Subgroup.mem_map.mpr ⟨⟨r, hrK⟩, ?_, rfl⟩
        rw [MonoidHom.mem_ker, hφ_apply]
        have hs1 : s ⟨r, hrK⟩ = 1 := Subtype.ext (by
          rw [hs]
          show RF.piB r = 1
          exact (RF.ker_piB.symm ▸ hr : r ∈ RF.piB.ker))
        rw [hs1]; simp
      have hXnormal : X.Normal := by
        rw [hXdef]
        refine ⟨fun x hx y => ?_⟩
        obtain ⟨k, hkker, hkeq⟩ := Subgroup.mem_map.mp hx
        have hxK : x ∈ Blk.K := hkeq ▸ k.2
        have hyk : y * x * y⁻¹ ∈ Blk.K := Blk.hK.conj_mem x hxK y
        refine Subgroup.mem_map.mpr ⟨⟨y * x * y⁻¹, hyk⟩, ?_, rfl⟩
        rw [MonoidHom.mem_ker] at hkker ⊢
        rw [hφ_apply] at hkker ⊢
        have hconj : Additive.ofMul (s ⟨y * x * y⁻¹, hyk⟩)
            = (QuotientGroup.mk (RF.piB y) : RF.YB ⧸ (En.radData l h).M)
                • Additive.ofMul (s ⟨x, hxK⟩) := by
          have hact : (QuotientGroup.mk (RF.piB y) : RF.YB ⧸ (En.radData l h).M)
                • Additive.ofMul (s ⟨x, hxK⟩)
              = Additive.ofMul (⟨Quotient.out (QuotientGroup.mk (RF.piB y)) * (s ⟨x, hxK⟩).1
                  * (Quotient.out (QuotientGroup.mk (RF.piB y)))⁻¹,
                  (En.radData l h).hM.conj_mem _ (s ⟨x, hxK⟩).2 _⟩ : ↥(En.radData l h).M) := rfl
          rw [hact]
          congr 1
          apply Subtype.ext
          rw [hs]
          show RF.piB (y * x * y⁻¹)
            = Quotient.out (QuotientGroup.mk (RF.piB y)) * (s ⟨x, hxK⟩).1
              * (Quotient.out (QuotientGroup.mk (RF.piB y)))⁻¹
          rw [hs, map_mul, map_mul, map_inv]
          exact (conj_eq_of_mk_eq_M (D := En.radData l h)
            (by rw [QuotientGroup.out_eq']) ⟨RF.piB x, hmem ⟨x, hxK⟩⟩).symm
        rw [hconj, hinv]
        have hkx : s ⟨x, hxK⟩ = s k := congrArg s (Subtype.ext hkeq.symm)
        rw [hkx]; exact hkker
      have hidx : (X.subgroupOf Blk.K).index = 2 := by
        have hcm : X.subgroupOf Blk.K = φ.ker := by
          rw [hXdef, Subgroup.subgroupOf,
            Subgroup.comap_map_eq_self_of_injective Blk.K.subtype_injective]
        show Nat.card (↥Blk.K ⧸ (X.subgroupOf Blk.K)) = 2
        rw [hcm, Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective φ hφsurj).toEquiv]
        simp
      exact absurd ⟨X, hXnormal, hRX, hXK, hidx⟩ (SectionSeven.lemma_7_1_dual Blk)
    rw [Nat.card_eq_one_iff_unique]
    exact ⟨⟨fun x y => Subtype.ext ((hzero x.val x.2).trans (hzero y.val y.2).symm)⟩,
      ⟨⟨0, fun c => smul_zero c⟩⟩⟩
  -- Step 2: the `Z¹`-torsor bridge (`MLifts` nonempty from `#H² = 1`, then `≃ Z¹`)
  have htorsor : Nat.card (MLifts (En.radData l h) (RF.rhoPrime b F (En.radData l h) rfl ρ))
      = Nat.card (Z1 AbsGalQ2 (Additive ↥(En.radData l h).M)) := by
    set ρ' := RF.rhoPrime b F (En.radData l h) rfl ρ with hρ'def
    -- **Nonemptiness**: `#H²(G_ℚ₂,M_B) = 1` kills the lift obstruction (extension splitting).
    have hne : Nonempty (MLifts (En.radData l h) ρ') := by
      haveI : IsTopologicalAddGroup (Additive ↥(En.radData l h).M) :=
        { continuous_add := continuous_of_discreteTopology
          continuous_neg := continuous_of_discreteTopology }
      haveI : DiscreteTopology RF.YB := RF.discB
      haveI : Finite RF.YB := RF.finiteB
      haveI : DiscreteTopology (RF.YB ⧸ (En.radData l h).M) := inferInstance
      -- a continuous set-section of `YB ↠ YB/M_B`
      set s : AbsGalQ2 → RF.YB := fun γ => Quotient.out (ρ' γ) with hsdef
      have hs_cont : Continuous s :=
        (continuous_of_discreteTopology (f := (Quotient.out :
          RF.YB ⧸ (En.radData l h).M → RF.YB))).comp ρ'.continuous_toFun
      have hs_mk : ∀ γ, (QuotientGroup.mk (s γ) : RF.YB ⧸ (En.radData l h).M) = ρ' γ :=
        fun γ => QuotientGroup.out_eq' _
      -- the action = conjugation by the section value
      have hsmul_s : ∀ (γ : AbsGalQ2) (a : Additive ↥(En.radData l h).M),
          γ • a = Additive.ofMul (⟨s γ * (Additive.toMul a).1 * (s γ)⁻¹,
              (En.radData l h).hM.conj_mem _ (Additive.toMul a).2 _⟩ : ↥(En.radData l h).M) := by
        intro γ a
        rw [hcomp]; apply Additive.toMul.injective; apply Subtype.ext
        show Quotient.out (ρ' γ) * (Additive.toMul a).1 * (Quotient.out (ρ' γ))⁻¹
          = s γ * (Additive.toMul a).1 * (s γ)⁻¹
        rfl
      -- the factor set `c(γ,δ) = s γ · s δ · s(γδ)⁻¹ ∈ M_B`
      have hc_mem : ∀ p : AbsGalQ2 × AbsGalQ2,
          s p.1 * s p.2 * (s (p.1 * p.2))⁻¹ ∈ (En.radData l h).M := by
        intro p
        rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_mul, QuotientGroup.mk_mul,
          QuotientGroup.mk_inv, hs_mk, hs_mk, hs_mk, ← map_mul, mul_inv_cancel]
      set c : AbsGalQ2 × AbsGalQ2 → Additive ↥(En.radData l h).M :=
        fun p => Additive.ofMul ⟨s p.1 * s p.2 * (s (p.1 * p.2))⁻¹, hc_mem p⟩ with hcdef
      have hc_Z2 : c ∈ Z2 AbsGalQ2 (Additive ↥(En.radData l h).M) := by
        rw [mem_Z2_iff]
        refine ⟨?_, ?_⟩
        · have hg : Continuous (fun p : AbsGalQ2 × AbsGalQ2 => s p.1 * s p.2 * (s (p.1 * p.2))⁻¹) :=
            (continuous_of_discreteTopology (f := fun t : RF.YB × RF.YB × RF.YB =>
                t.1 * t.2.1 * t.2.2⁻¹)).comp
              ((hs_cont.comp continuous_fst).prodMk ((hs_cont.comp continuous_snd).prodMk
                (hs_cont.comp (continuous_fst.mul continuous_snd))))
          exact hg.subtype_mk _
        · intro x y z
          rw [hsmul_s x (c (y, z))]
          apply Additive.toMul.injective
          -- both sides are products in the CommGroup `↥M_B`; reorder then compare `.1` in `YB`
          show (⟨s x * (s y * s z * (s (y * z))⁻¹) * (s x)⁻¹, _⟩ : ↥(En.radData l h).M)
              * ⟨s x * s (y * z) * (s (x * (y * z)))⁻¹, _⟩
            = ⟨s (x * y) * s z * (s ((x * y) * z))⁻¹, _⟩
              * ⟨s x * s y * (s (x * y))⁻¹, _⟩
          rw [mul_comm (⟨s (x * y) * s z * (s ((x * y) * z))⁻¹, _⟩ : ↥(En.radData l h).M) _]
          apply Subtype.ext
          show s x * (s y * s z * (s (y * z))⁻¹) * (s x)⁻¹ * (s x * s (y * z) * (s (x * (y * z)))⁻¹)
            = s x * s y * (s (x * y))⁻¹ * (s (x * y) * s z * (s ((x * y) * z))⁻¹)
          rw [mul_assoc x y z]; group
      -- `#H² = 1` ⟹ `c` is a coboundary
      have hH2 : Nat.card (H2 AbsGalQ2 (Additive ↥(En.radData l h).M)) = 1 :=
        (card_H2_eq_fixedPts hρ's hcomp hA₂).trans hfix
      haveI : Subsingleton (H2 AbsGalQ2 (Additive ↥(En.radData l h).M)) :=
        (Nat.card_eq_one_iff_unique.mp hH2).1
      have hcB2 : c ∈ B2 AbsGalQ2 (Additive ↥(En.radData l h).M) := by
        have h0 : H2mk AbsGalQ2 (Additive ↥(En.radData l h).M) ⟨c, hc_Z2⟩ = 0 :=
          Subsingleton.elim _ _
        exact AddSubgroup.mem_addSubgroupOf.mp ((QuotientAddGroup.eq_zero_iff _).mp h0)
      obtain ⟨ψ, hψc, hψ⟩ := hcB2
      -- the lift `f γ = (toMul (ψ γ))⁻¹ · s γ`
      set ψ' : AbsGalQ2 → RF.YB := fun γ => (Additive.toMul (ψ γ)).1 with hψ'def
      have hψ'mem : ∀ γ, ψ' γ ∈ (En.radData l h).M := fun γ => (Additive.toMul (ψ γ)).2
      -- read off the coboundary identity in `YB` (all `toMul`/`.1` reductions are defeq)
      have hrel : ∀ x y : AbsGalQ2,
          s x * ψ' y * (s x)⁻¹ * (ψ' (x * y))⁻¹ * ψ' x = s x * s y * (s (x * y))⁻¹ := by
        intro x y
        have hxy_eq : x • ψ y - ψ (x * y) + ψ x = c (x, y) := congrFun hψ (x, y)
        rw [hsmul_s x (ψ y)] at hxy_eq
        have hxy := congrArg (fun a : Additive ↥(En.radData l h).M => (Additive.toMul a).1) hxy_eq
        simpa [hcdef, hψ'def, div_eq_mul_inv, mul_assoc] using hxy
      refine ⟨⟨⟨MonoidHom.mk' (fun γ => (ψ' γ)⁻¹ * s γ) (fun x y => ?_), ?_⟩, ?_⟩⟩
      · -- homomorphism: `f(xy) = f x · f y`, from `hrel` + `ψ'x,ψ'(xy) ∈ M` commuting
        have hcomm : Commute (ψ' (x * y)) (ψ' x) :=
          (En.radData l h).hcomm _ (hψ'mem (x * y)) _ (hψ'mem x)
        show (ψ' (x * y))⁻¹ * s (x * y) = (ψ' x)⁻¹ * s x * ((ψ' y)⁻¹ * s y)
        have hs_xy : s (x * y) = (ψ' x)⁻¹ * ψ' (x * y) * s x * (ψ' y)⁻¹ * s y := by
          have e : s (x * y)
              = (s x * ψ' y * (s x)⁻¹ * (ψ' (x * y))⁻¹ * ψ' x)⁻¹ * (s x * s y) := by
            rw [hrel x y]; group
          rw [e]; group
        rw [hs_xy]
        rw [show (ψ' (x * y))⁻¹ * ((ψ' x)⁻¹ * ψ' (x * y) * s x * (ψ' y)⁻¹ * s y)
            = ((ψ' (x * y))⁻¹ * (ψ' x)⁻¹ * ψ' (x * y)) * (s x * (ψ' y)⁻¹ * s y) from by group,
          show (ψ' (x * y))⁻¹ * (ψ' x)⁻¹ * ψ' (x * y) = (ψ' x)⁻¹ from by
            rw [mul_assoc, (hcomm.symm.inv_left).eq, ← mul_assoc, inv_mul_cancel, one_mul]]
        group
      · -- continuity
        have hψ'cont : Continuous ψ' :=
          (continuous_of_discreteTopology (f := fun a : Additive ↥(En.radData l h).M =>
            (Additive.toMul a).1)).comp hψc
        exact (continuous_of_discreteTopology (f := fun p : RF.YB × RF.YB => p.1⁻¹ * p.2)).comp
          (hψ'cont.prodMk hs_cont)
      · -- over `ρ'`
        intro γ
        show QuotientGroup.mk ((ψ' γ)⁻¹ * s γ) = ρ' γ
        rw [QuotientGroup.mk_mul, (QuotientGroup.eq_one_iff _).mpr (inv_mem (hψ'mem γ)),
          one_mul, hs_mk]
    obtain ⟨f₀⟩ := hne
    -- the `G_ℚ₂`-action on `M_B` is conjugation by the lift `f₀ γ` of `ρ' γ`
    have hsmul : ∀ (γ : AbsGalQ2) (a : Additive ↥(En.radData l h).M),
        γ • a = Additive.ofMul (⟨f₀.1 γ * (Additive.toMul a).1 * (f₀.1 γ)⁻¹,
              (En.radData l h).hM.conj_mem _ (Additive.toMul a).2 _⟩ : ↥(En.radData l h).M) := by
      intro γ a
      rw [hcomp]
      apply Additive.toMul.injective; apply Subtype.ext
      show Quotient.out (ρ' γ) * (Additive.toMul a).1 * (Quotient.out (ρ' γ))⁻¹
        = f₀.1 γ * (Additive.toMul a).1 * (f₀.1 γ)⁻¹
      exact conj_eq_of_mk_eq_M (D := En.radData l h)
        (by rw [QuotientGroup.out_eq', f₀.2 γ]) (Additive.toMul a)
    have hmemf : ∀ (f : MLifts (En.radData l h) ρ') (γ : AbsGalQ2),
        f.1 γ * (f₀.1 γ)⁻¹ ∈ (En.radData l h).M := by
      intro f γ
      have heq : (QuotientGroup.mk (f.1 γ) : RF.YB ⧸ (En.radData l h).M)
          = QuotientGroup.mk (f₀.1 γ) := (f.2 γ).trans (f₀.2 γ).symm
      have := QuotientGroup.eq_iff_div_mem.mp heq
      rwa [div_eq_mul_inv] at this
    refine Nat.card_congr
      { toFun := fun f => ⟨fun γ => Additive.ofMul ⟨f.1 γ * (f₀.1 γ)⁻¹, hmemf f γ⟩, ?_⟩
        invFun := fun c => ⟨⟨MonoidHom.mk'
            (fun γ => (Additive.toMul (c.1 γ)).1 * f₀.1 γ) ?_, ?_⟩, ?_⟩
        left_inv := ?_
        right_inv := ?_ }
    · -- forward lands in `Z¹`
      rw [mem_Z1_iff]
      refine ⟨?_, ?_⟩
      · have hg : Continuous (fun γ : AbsGalQ2 => f.1 γ * (f₀.1 γ)⁻¹) :=
          (continuous_of_discreteTopology (f := fun p : RF.YB × RF.YB => p.1 * p.2⁻¹)).comp
            (f.1.continuous_toFun.prodMk f₀.1.continuous_toFun)
        exact hg.subtype_mk (hmemf f)
      · intro g s
        rw [hsmul g (Additive.ofMul ⟨f.1 s * (f₀.1 s)⁻¹, hmemf f s⟩)]
        apply Additive.toMul.injective; apply Subtype.ext
        show f.1 (g * s) * (f₀.1 (g * s))⁻¹
          = f.1 g * (f₀.1 g)⁻¹ * (f₀.1 g * (f.1 s * (f₀.1 s)⁻¹) * (f₀.1 g)⁻¹)
        rw [map_mul, map_mul]; group
    · -- inverse is a hom
      intro g h
      show (Additive.toMul (c.1 (g * h))).1 * f₀.1 (g * h)
        = (Additive.toMul (c.1 g)).1 * f₀.1 g * ((Additive.toMul (c.1 h)).1 * f₀.1 h)
      rw [(mem_Z1_iff.mp c.2).2 g h, map_mul, hsmul g (c.1 h)]
      show (Additive.toMul (c.1 g)).1 * (f₀.1 g * (Additive.toMul (c.1 h)).1 * (f₀.1 g)⁻¹)
          * (f₀.1 g * f₀.1 h) = _
      group
    · -- inverse is continuous
      exact (continuous_of_discreteTopology
          (f := fun p : Additive ↥(En.radData l h).M × RF.YB => (Additive.toMul p.1).1 * p.2)).comp
        ((mem_Z1_iff.mp c.2).1.prodMk f₀.1.continuous_toFun)
    · -- inverse lands over `ρ'`
      intro γ
      show QuotientGroup.mk ((Additive.toMul (c.1 γ)).1 * f₀.1 γ) = ρ' γ
      rw [QuotientGroup.mk_mul,
        (QuotientGroup.eq_one_iff ((Additive.toMul (c.1 γ)).1)).mpr (Additive.toMul (c.1 γ)).2,
        one_mul, f₀.2 γ]
    · -- left inverse
      intro f
      apply Subtype.ext; apply ContinuousMonoidHom.ext; intro γ
      show f.1 γ * (f₀.1 γ)⁻¹ * f₀.1 γ = f.1 γ
      group
    · -- right inverse
      intro c
      apply Subtype.ext; funext γ
      show Additive.ofMul (⟨(Additive.toMul (c.1 γ)).1 * f₀.1 γ * (f₀.1 γ)⁻¹, _⟩
          : ↥(En.radData l h).M) = c.1 γ
      rw [show (⟨(Additive.toMul (c.1 γ)).1 * f₀.1 γ * (f₀.1 γ)⁻¹, _⟩ : ↥(En.radData l h).M)
          = Additive.toMul (c.1 γ) from Subtype.ext (by group)]
      rfl
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
