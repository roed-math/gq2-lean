import GQ2.RadicalEdgeBridge
import GQ2.AffineTLift

/-!
# P-16d6b: μ-independence of the `T`-cocycle count  (torsor reduction to the source counts)

The (140) engine (`zBC_eq_mu_mul_reductionCount`, `phase140_of_nonsingular`) consumes a constant
`μ` with `hμ : ∀ ρ, Nat.card (TCocycle D (rhoPrime ρ)) = μ` — the crossed count `#Z¹_{Γ,ρ}(T)` is
**independent of the exact-image map `ρ`** (paper 5.15/5.16 content).

## Why not Route B literally

The handoff's Route B computes the count by `prop_5_16_bundle` clause 2
(`#Z¹ = |T|² · |fixedPts(ρ(Γ), T^∨)|`) and reads off ρ-independence from `ρ(Γ) = C`.  But
`prop_5_16_bundle` — and its building blocks `card_Z1_eq` / `card_H2_eq_fixedPts` — are stated over
**`AbsGalQ2`** specifically (they carry B6/B7: Tate duality + the local Euler characteristic for
`G_ℚ₂`).  This file's deliverable `tcocycle_mu_indep`, and its consumer
`zBC_eq_mu_mul_reductionCount`, are stated over a **generic `Γ`** (any profinite group).  For a
generic `Γ` the count *value* `#Z¹_{Γ,ρ}(T)` is genuinely source-dependent — Euler characteristic
and Tate duality are false for an arbitrary profinite group — so **no single generic Route-B proof
exists**, and `prop_5_16_bundle` cannot even be invoked here (`Γ ≠ AbsGalQ2`).  This is exactly the
§6 risk of `docs/p16d6b-handoff.md`, and it is structural, not incidental.

## The idiomatic resolution (handoff §6 option 3) — torsor reduction to per-source counts

The sibling obligation is discharged the same way: `half139_via_radData` (in `RecursionSplice.lean`)
does **not** prove the `#MLifts = |M_B|²` count generically — it *takes it as a per-source
hypothesis* `hMcountM` fed by the assembly, where `Γ` is a concrete source (`G_ℚ₂` or `Γ_A`) with its
own duality theorem (`prop_5_16_bundle` resp. the `Γ_A`/`prop_5_15` analog in `HalfTorsorGammaA` /
`RadicalEdgeGammaA`).  We follow the same pattern for `#Z¹(T)`.

The genuine, `Γ`-generic content proved here is the **torsor count identity**
`#MLifts = #(red_T image) · #Z¹(T)` (`mlifts_card_eq_image_mul_tcocycle`): every `red_T`-fibre over
`MLifts` is a `Z¹_{Γ,ρ}(T)`-torsor (`tcocycle_torsor_equiv`), so the total `M`-lift count factors
through the reduction image.  ρ-independence of `#Z¹(T)` then follows by cancellation from
ρ-independence of the two source counts:

* `#MLifts(ρ)` — the `M`-lift count `|M_B|²` (props 5.15/5.16; = `half139`'s `hMcountM`);
* `#(red_T image over MLifts)(ρ)` — the `B/T`-lift count (the same 5.15/5.16 content one cover down).

Both depend only on the target data (`M_B`, `T`), not on `ρ`, at each source; the assembly
(P-16d6e) supplies them concretely per source.  This makes the whole file **std-3, sorry-free**
(`Ax ∅`) — the B6/B7 duality content sits, correctly, in the fed hypotheses, exactly as for
`half139_via_radData`.

This file (own leaf, off the co-owned `RecursionSplice.lean`) banks:
* `boundaryLift_diff_mem_LY` — the shared-boundary fact (`ρ'/ρ ∈ L_C`); **proved**, std-3.
* `mlifts_card_eq_image_mul_tcocycle` — the `Γ`-generic torsor count identity; **proved**, std-3.
* `tcocycle_card_indep` — the pairwise ρ-independence core, conditional on the two source counts;
  **proved**, std-3.
* `tcocycle_mu_indep` — the `∃μ` packaging in the consumers' shape, conditional on the two source
  counts (fed constants `κ_M`, `κ_I`); **proved**, std-3.
-/

namespace GQ2

namespace SectionEight

open CentralObstruction AffineTLift

variable {H E : Type} [Group H] [TopologicalSpace H] [DiscreteTopology H] [Finite H]
  [CommGroup E] [TopologicalSpace E] [DiscreteTopology E] [Finite E]
variable {Γ : Type} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [CompactSpace Γ]
  [TotallyDisconnectedSpace Γ]
variable {Y : Type} [Group Y] [TopologicalSpace Y] [DiscreteTopology Y] [Finite Y]
variable {T : MarkedTarget H E Y} {Blk : SectionSeven.MinimalBlock T.LY} (RF : RecursionFrame T Blk)
variable (b : ContinuousMonoidHom Γ ↥boundarySubgroup) (F : BoundaryFrame H E)
variable (D : RadicalCoverData RF.YB) (hD : D.M = RF.MB)

omit [IsTopologicalGroup Γ] [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
  [TopologicalSpace Y] [DiscreteTopology Y] in
/-- **Shared-boundary fact**: two boundary lifts of the same `C`-target agree after `π_Y`, so their
ratio lands in `ker π_Y = L_C = RF.TC.LY`.  (Banked; used nowhere on the torsor route, but a true
lemma about boundary lifts — keep it.) -/
theorem boundaryLift_diff_mem_LY (ρ ρ' : BoundaryLifts b F RF.TC) (γ : Γ) :
    ρ'.1.1 γ * (ρ.1.1 γ)⁻¹ ∈ RF.TC.LY := by
  have hρ := (ρ.2 γ)
  have hρ' := (ρ'.2 γ)
  -- both first components equal `(F.frameMap (b γ)).1`, so the `π_Y`-images agree
  have hpi : RF.TC.piY (ρ'.1.1 γ) = RF.TC.piY (ρ.1.1 γ) := by
    have h1 : RF.TC.piY (ρ.1.1 γ) = (F.frameMap (b γ)).1 := congrArg Prod.fst hρ
    have h2 : RF.TC.piY (ρ'.1.1 γ) = (F.frameMap (b γ)).1 := congrArg Prod.fst hρ'
    rw [h1, h2]
  rw [← RF.TC.ker_piY, MonoidHom.mem_ker, map_mul, map_inv, hpi, mul_inv_cancel]

/-- **The torsor count identity** (`Γ`-generic, std-3): the total `M`-lift count factors as
`#MLifts = #(red_T image) · #Z¹_{Γ,ρ}(T)`.  Each `red_T`-fibre over `MLifts` is a
`Z¹_{Γ,ρ}(T)`-torsor (`tcocycle_torsor_equiv`), so summing over the (finite) reduction image gives
the product.  (This is the all-lifts analog of `central_card_eq_reductions_mul_tcocycle`, and is in
fact simpler — no `Descent`/`lemma_8_7_count`, since `tcocycle_torsor_equiv` computes every fibre
directly, not only the central ones.) -/
theorem mlifts_card_eq_image_mul_tcocycle
    {Bg : Type} [Group Bg] [Finite Bg] [TopologicalSpace Bg] [DiscreteTopology Bg]
    {D : RadicalCoverData Bg}
    {Γ' : Type} [Group Γ'] [TopologicalSpace Γ'] [IsTopologicalGroup Γ']
    [CompactSpace Γ'] [TotallyDisconnectedSpace Γ']
    [DistribMulAction Γ' (ZMod 2)] [ContinuousSMul Γ' (ZMod 2)]
    (ρ : ContinuousMonoidHom Γ' (Bg ⧸ D.M))
    (hfg : ∃ s : Finset Γ', (Subgroup.closure (s : Set Γ')).topologicalClosure = ⊤) :
    Nat.card (MLifts D ρ)
      = Nat.card ↥(Set.range (fun f : MLifts D ρ => redT ρ f)) * Nat.card (TCocycle D ρ) := by
  classical
  haveI : Finite (ContinuousMonoidHom Γ' Bg) := finite_continuousMonoidHom hfg Bg
  haveI : Finite (MLifts D ρ) := Subtype.finite
  set img : Set (Γ' → Bg ⧸ D.T) := Set.range (fun f : MLifts D ρ => redT ρ f) with himg
  haveI : Fintype ↥img := Fintype.ofFinite _
  -- each fibre of `red_T` over its range is a `Z¹(T)`-torsor
  have hfibre : ∀ r : ↥img,
      Nat.card {f : MLifts D ρ // (⟨redT ρ f, f, rfl⟩ : ↥img) = r} = Nat.card (TCocycle D ρ) := by
    intro r
    obtain ⟨f₀, hf₀⟩ := r.2
    calc Nat.card {f : MLifts D ρ // (⟨redT ρ f, f, rfl⟩ : ↥img) = r}
        = Nat.card {f : MLifts D ρ // redT ρ f = r.1} :=
          Nat.card_congr (Equiv.subtypeEquivRight fun _ => Subtype.ext_iff)
      _ = Nat.card {f : MLifts D ρ // redT ρ f = redT ρ f₀} := by rw [← hf₀]
      _ = Nat.card (TCocycle D ρ) := (Nat.card_congr (tcocycle_torsor_equiv ρ f₀)).symm
  calc Nat.card (MLifts D ρ)
      = Nat.card (Σ r : ↥img, {f : MLifts D ρ // (⟨redT ρ f, f, rfl⟩ : ↥img) = r}) :=
        (Nat.card_congr (Equiv.sigmaFiberEquiv
          (fun f : MLifts D ρ => (⟨redT ρ f, f, rfl⟩ : ↥img)))).symm
    _ = ∑ r : ↥img, Nat.card {f : MLifts D ρ // (⟨redT ρ f, f, rfl⟩ : ↥img) = r} := Nat.card_sigma
    _ = ∑ _r : ↥img, Nat.card (TCocycle D ρ) := Finset.sum_congr rfl (fun r _ => hfibre r)
    _ = Nat.card ↥img * Nat.card (TCocycle D ρ) := by
        rw [Finset.sum_const, Finset.card_univ, smul_eq_mul, ← Nat.card_eq_fintype_card]

-- the `Γ`-action on `ZMod 2` carried by `redT`/`tcocycle_torsor_equiv` (AffineTLift `Count`
-- section); the consumers (`zBC_eq_mu_mul_reductionCount`, …) already assume it.
variable [DistribMulAction Γ (ZMod 2)] [ContinuousSMul Γ (ZMod 2)]

/-- **P-16d6b core**: `#Z¹_{Γ,ρ}(T)` is the same for any two boundary lifts of the `C`-target,
*given* that the two source counts (`#MLifts` and the `red_T`-image count) are ρ-independent.

The count value is genuinely source-specific (see the module docstring), so ρ-independence is not
derivable for a generic `Γ` without a duality input.  We supply that input in the idiom of
`half139_via_radData`'s `hMcountM`: the two per-source counts

* `hML` : `#MLifts(ρ) = #MLifts(ρ')` — the `|M_B|²` count (props 5.15/5.16), and
* `hIMG` : `#(red_T image)(ρ) = #(red_T image)(ρ')` — the `B/T`-lift count,

both of which depend only on the target `(M_B, T)` and are discharged per source at the P-16d6e
assembly.  Cancellation through the torsor identity (`hIne` : the reduction image is nonempty, which
holds whenever `ρ` admits an `M`-lift, i.e. `#MLifts ≠ 0`) then forces the `Z¹`-counts to agree. -/
theorem tcocycle_card_indep (ρ ρ' : BoundaryLifts b F RF.TC)
    (hfg : ∃ s : Finset Γ, (Subgroup.closure (s : Set Γ)).topologicalClosure = ⊤)
    (hML : Nat.card (MLifts D (RF.rhoPrime b F D hD ρ))
             = Nat.card (MLifts D (RF.rhoPrime b F D hD ρ')))
    (hIMG : Nat.card ↥(Set.range (fun f : MLifts D (RF.rhoPrime b F D hD ρ) =>
              redT (RF.rhoPrime b F D hD ρ) f))
              = Nat.card ↥(Set.range (fun f : MLifts D (RF.rhoPrime b F D hD ρ') =>
                redT (RF.rhoPrime b F D hD ρ') f)))
    (hIne : Nat.card ↥(Set.range (fun f : MLifts D (RF.rhoPrime b F D hD ρ) =>
              redT (RF.rhoPrime b F D hD ρ) f)) ≠ 0) :
    Nat.card (TCocycle D (RF.rhoPrime b F D hD ρ))
      = Nat.card (TCocycle D (RF.rhoPrime b F D hD ρ')) := by
  have e1 := mlifts_card_eq_image_mul_tcocycle (RF.rhoPrime b F D hD ρ) hfg
  have e2 := mlifts_card_eq_image_mul_tcocycle (RF.rhoPrime b F D hD ρ') hfg
  -- `#img(ρ)·#TC(ρ) = #MLifts(ρ) = #MLifts(ρ') = #img(ρ')·#TC(ρ') = #img(ρ)·#TC(ρ')`
  rw [e1, e2, ← hIMG] at hML
  exact Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hIne) hML

/-- **P-16d6b deliverable**: the `T`-cocycle count is `ρ`-independent — the constant `μ` and the
`hμ` hypothesis consumed by `zBC_eq_mu_mul_reductionCount` / `phase140_of_nonsingular`.

Conditional on the two per-source counts as fixed constants (`κ_M = #MLifts`, `κ_I = #(red_T image)`,
both `ρ`-independent and dischargeable at the source; `hIne : κ_I ≠ 0`), the torsor identity pins
every `#Z¹(T)` to `κ_M / κ_I`.  The assembly (P-16d6e) feeds `κ_M` from `hMcountM` and `κ_I` from
the `B/T`-lift count, both from the source's 5.15/5.16 duality theorem. -/
theorem tcocycle_mu_indep
    (hfg : ∃ s : Finset Γ, (Subgroup.closure (s : Set Γ)).topologicalClosure = ⊤)
    (κM κI : ℕ) (hIne : κI ≠ 0)
    (hML : ∀ ρ : BoundaryLifts b F RF.TC, Nat.card (MLifts D (RF.rhoPrime b F D hD ρ)) = κM)
    (hIMG : ∀ ρ : BoundaryLifts b F RF.TC,
      Nat.card ↥(Set.range (fun f : MLifts D (RF.rhoPrime b F D hD ρ) =>
        redT (RF.rhoPrime b F D hD ρ) f)) = κI) :
    ∃ μ : ℕ, ∀ ρ : BoundaryLifts b F RF.TC,
      Nat.card (TCocycle D (RF.rhoPrime b F D hD ρ)) = μ := by
  refine ⟨κM / κI, fun ρ => ?_⟩
  have e := mlifts_card_eq_image_mul_tcocycle (RF.rhoPrime b F D hD ρ) hfg
  rw [hML ρ, hIMG ρ] at e
  -- `e : κM = κI * #TC(ρ)`, so `#TC(ρ) = κM / κI`
  rw [e, Nat.mul_div_cancel_left _ (Nat.pos_of_ne_zero hIne)]

end SectionEight

end GQ2
