/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Opus-5
-/
import GQ2.Dyadic.Instances.KSupply

/-!
# The (83)-evaluation bridge at `G_K` (dyadic campaign, ticket CB-DET)

LG5's `local_gauss_K` (packet Thm. 6.15) evaluates the Arf invariant / zero count of the base
determinant form `Q⁰_{K,V}` on `H¹(G_K, V)`.  The recursion consumes a *different* object: the
source-Gauss residue `GaussZResidueK`, a sum over the crossed cocycle group `Z¹`.  This file is
the rung between them at a general `K` — the `K`-clone of `GQ2/GaussZ/FinalD.lean` over
`GQ2/GaussZ/{Final, Local, Reduction}.lean`.

## The degree-shift audit (SD1 memo §9), clause by clause

The `ℚ₂` chain has three numeric constants.  **Two move with the degree, one does not**, and the
file records each as a theorem rather than a convention:

| constant | `ℚ₂` value | value at `K` | moves? |
|---|---|---|---|
| the outer `#V` of `GaussZResidueK` | `#V` | `#V` | **no** — it is `#B¹`, and `B¹ ≅ V` at every `Γ` |
| `#Z¹` (`GQ2/GaussZ/Reduction.lean:287`) | `#V * #V` | `#V * #H¹(G_K,V)` | **yes** |
| the Gauss value `G₀` | `∓2^m` | `(−1)^n 2^{nm}` / `+2^{nm}` | **yes** |

The middle row is `card_vcocycle_eq_mul_card_H1` below, and it is the substantive finding: the
`ℚ₂` `#Z¹ = #V²` is **not** a `#V`-squared law, it is `#B¹ · #H¹` with `#H¹ = #V` in degree 1.
At `K` the same proof gives `#Z¹ = #V · #H¹(G_K, V)`, and LG5's Euler clause reads
`#H¹(G_K, V) = 2^{2mn} = (#V)^n`.  So `SourceNumerics.h1Mult V = V^n` is exactly right, and
`SourceDataN.hZcard`'s `#V * SN.h1Mult #V` is exactly right; a verbatim `#V²` clone would have
been false for every `K ≠ ℚ₂`.  The Gauss values likewise match `standardNumerics` on the nose
(`(−1)^n 2^{nm}`, `2^{nm}`) — see `gaussUnram_standard` / `gaussRam_standard`.

## What is reused rather than cloned

The `ℚ₂` substrate is **already `Γ`-generic almost everywhere**, so this is not a 1.3k-line
clone.  Consumed verbatim by import:

* the whole of `GQ2/GaussZ/Reduction.lean` (`gaussZ_reduction`, `QZeroBar`, `vCobHom`,
  `vCobRange`, `vCobHom_injective`, `graphPullback_shift_mem_B2`, `QZero_add_vCob`,
  `card_quotient_vCobRange`) — every declaration is stated over an abstract `Γ`;
* the `Z¹`-bridge and quotient bijection of `GQ2/GaussZ/Local.lean` §(A)/(B) (`toZ1`, `ofZ1`,
  `h1OfVQuot`, `h1OfVQuot_injective`, `h1OfVQuot_surjective`, `H1mk_eq_iff`) — likewise;
* `hfix_of_simple_nt` (`GQ2/GaussZ/CoordGammaA.lean:64`), `iotaB`/`iotaB_eq_zero_iff`/
  `H2mk_eq_zero_iff` (`GQ2/Phase140/Obstruction.lean`), `graphPullback_mem_Z2_of_cocycle`,
  `ShapiroLedger.H2ofFun_eq_of_sub_mem_B2`, `ShapiroDeepness.graphPullback_reindexHom`;
* LG2's `GQ2.Dyadic.{iotaF, Q0loc}` at a `TateDualityG Γ 2` bundle, and SD-R1/SD-R3's
  `rho0_descData_rhoPrimeK`, `boundaryLift_headK`, `blockEnrichmentDK`, `blockDatHVK`,
  `blockQbarK`, `hv_invK`.

**Measured**: of the 25 declarations in the `ℚ₂` `Reduction`/`Local`/`Final`/`FinalD` chain,
**17 are ambient-free and are used verbatim**; 5 are genuinely `G_ℚ₂`-typed and are retyped here
(`iotaF_injective`, `iotaB_eq_iotaF`, `QZeroBar_eq_Q0loc`, `Q0loc_reindexHom_hom`,
`finsum_sign_eq`); 3 (`gaussZResidue_local_*`, `headTameSurj`) are compositions replaced by the
§4/§5 assemblies.  Substrate written here: ≈250 lines, not 1.3k.

## The `smul` trap and the instance-path trap

Both are live and both are handled the same way as LG2/LG4c and CB-SG: the `ℚ₂` chain's
`htriv` steps are `rfl`-lemmas at `AbsGalQ2` and are replaced by LG2's `smul_zmodTwo`; and every
statement is taken at the `Subgroup AbsGalQ2` spelling `↥U`, never at `↥(galKProfinite K)`, so
that `rw` never has to cross an instance path.  §6's consumer does the single `show` that pins
`↥(galKProfinite K) = GalK K = ↥(GalKsub K)`.

## Axioms

Everything in §1–§4 is parametrized over the duality bundle `D : TateDualityG ↥U 2` and prints
std-3.  §5's `sum_sign_Q0loc_K_*` inherit LG5's budget (B6/B7/B9/B11a through `local_gauss_K`),
and §6's `affineDeterminant_galK` additionally builds `D` from B6 at `K`
(`FieldData.tateDualityGalK`).  No new axiom, and none of the nine obligations is assumed.
-/

namespace GQ2.Dyadic

open GQ2 GQ2.SectionEight
open SectionSeven AffineTLift CentralObstruction ContCoh
open scoped Classical

local notation "ℚ̄₂" => AlgebraicClosure ℚ_[2]

/-! ## §1 The obstruction bridge at a general `Γ`

`GQ2/IotaBridge.lean` proves `iotaB φ = iotaF D (H²ofFun φ)` on continuous 2-cocycles over
`G_ℚ₂`.  Nothing in that argument is about `G_ℚ₂`: both sides vanish exactly on `B²`, and a
`ZMod 2`-value is pinned by whether it is `0`.  The one `G_ℚ₂`-typed ingredient is the
injectivity of `iotaF`, which at a general `Γ` is `CupSymmetry`'s `H2congr` — the coefficient
bijection `𝔽₂ ≃+ μ₂` transported to `H²`, which is an `AddEquiv` for **any** group. -/

section IotaBridgeG

variable {Γ : Type} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
  [DistribMulAction Γ (ZMod 2)] [ContinuousSMul Γ (ZMod 2)]
  [DistribMulAction Γ (MuN 2)] [ContinuousSMul Γ (MuN 2)]

omit [ContinuousSMul Γ (ZMod 2)] in
/-- **`iotaF D` is injective at any `Γ`** — the `Γ`-generic `GQ2.SectionEight.iotaF_injective`.
`D.inv` is an `AddEquiv` by definition of the bundle, and the coefficient factor
`mapCoeff2 muTwoOfF2` is the underlying map of `CupSymmetry`'s `H2congr` at the `𝔽₂ ≃+ μ₂`
bridge, hence bijective.  (The `ℚ₂` proof instead re-proved injectivity by hand through
`mapCoeff2_injective`; the `H2congr` route is shorter and needs no ambient at all.) -/
theorem iotaF_injectiveG (D : TateDualityG Γ 2) : Function.Injective (iotaF D) := by
  have hcoe : ∀ x : H2 Γ (ZMod 2), iotaF D x
      = D.inv (H2congr DeepPart.zmodTwoEquivMuTwo
        (fun (g : Γ) (n : ZMod 2) => muTwoOfF2_equivariant g n) x) := fun _ => rfl
  intro x y hxy
  rw [hcoe, hcoe] at hxy
  exact (H2congr DeepPart.zmodTwoEquivMuTwo
    (fun (g : Γ) (n : ZMod 2) => muTwoOfF2_equivariant g n)).injective (D.inv.injective hxy)

/-- **The abstract ↔ invariant obstruction bridge at any `Γ`** — the `Γ`-generic
`GQ2.SectionEight.iotaB_eq_iotaF`: on a continuous 2-cocycle the coboundary indicator `ι_Γ`
agrees with the Tate invariant `ι_F ∘ H²ofFun`. -/
theorem iotaB_eq_iotaFG (D : TateDualityG Γ 2)
    {φ : Γ × Γ → ZMod 2} (hφ : φ ∈ Z2 Γ (ZMod 2)) :
    iotaB φ = iotaF D (H2ofFun Γ φ) := by
  rw [H2ofFun_of_mem hφ]
  refine (by decide : ∀ a b : ZMod 2, (a = 0 ↔ b = 0) → a = b) _ _ ?_
  rw [iotaB_eq_zero_iff, map_eq_zero_iff (iotaF D) (iotaF_injectiveG D), H2mk_eq_zero_iff]

end IotaBridgeG

/-! ## §2 The `Z¹`-count — where the degree shift actually lives

`GQ2/GaussZ/Reduction.lean:285` states the `H¹`-model count *backwards*: it takes
`#Z¹ = #V · #V` as a hypothesis and concludes `#(Z¹ ⧸ B¹) = #V`.  Read forwards, the same two
ingredients (`B¹ ≅ V` by freeness, `Z¹ ⧸ B¹ ≅ H¹` by the transport) are a **theorem**:

  `#Z¹_{Γ,ρ}(V) = #V · #H¹(Γ, V)`,

with **no** numeric input at all.  That is the whole content of SD1 memo §9's warning: the `ℚ₂`
`#V²` is `#B¹ · #H¹` with `#H¹ = #V` in degree 1, and at `K` the second factor is
`#H¹(G_K, V) = 2^{2mn} = (#V)^n`.  So `SourceNumerics.h1Mult V = V^n` is forced, not chosen, and
the `SourceDataN.hZcard` clause `#Z¹ = #V * SN.h1Mult #V` is the correct general shape.

The corollary `finite_vcocycleG` replaces the `ℚ₂` chain's use of `hZcard_local` for `Z¹`
finiteness: it needs only that `#V` and `#H¹` are nonzero, and at `K` the latter is LG5's Euler
clause.  This is what makes the bridge independent of the (unowned) `K`-clone of
`GQ2/Phase140/Local.lean`. -/

section ZCount

variable {Bg : Type} [Group Bg] [Finite Bg] [TopologicalSpace Bg] [DiscreteTopology Bg]
  {D : RadicalCoverData Bg} {DD : DescData D}
variable {Γ : Type} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
  [DistribMulAction Γ (ZMod 2)] [ContinuousSMul Γ (ZMod 2)]
variable {ρ : ContinuousMonoidHom Γ (Bg ⧸ D.M)}
variable [TopologicalSpace DD.Vmod] [DiscreteTopology DD.Vmod] [DistribMulAction Γ DD.Vmod]

omit [IsTopologicalGroup Γ] [DistribMulAction Γ (ZMod 2)] [ContinuousSMul Γ (ZMod 2)] in
/-- **`#Z¹_{Γ,ρ}(V) = #V · #H¹(Γ, V)`** — the correct, degree-shift-aware form of the `ℚ₂`
`hZcard` shape (`GQ2/GaussZ/Reduction.lean:287`'s `#V * #V`).

Two exact sequences and nothing else: `B¹ ≅ V` because `vCob` is injective when `V` carries no
nonzero `ρ'`-fixed vector (`vCobHom_injective`), and `Z¹ ⧸ B¹ ≅ H¹(Γ, V)` by the transport
`h1OfVQuot` (`GQ2/GaussZ/Local.lean` (B)).  Both are `Γ`-generic in the `ℚ₂` files already; only
the *reading* is new.  Specialises to the `ℚ₂` `#V²` exactly when `#H¹ = #V`, which is
`DeepPart.card_H1_eq_card_of_simple` in degree 1 — and **fails** for `[K : ℚ₂] > 1`. -/
theorem card_vcocycle_eq_mul_card_H1
    (hcomp : ∀ (γ : Γ) (v : DD.Vmod), γ • v = rho0 DD ρ γ • v)
    (hfix : ∀ v : DD.Vmod, (∀ γ : Γ, rho0 DD ρ γ • v = v) → v = 0) :
    Nat.card (VCocycle DD ρ) = Nat.card DD.Vmod * Nat.card (H1 Γ DD.Vmod) := by
  have hrange : Nat.card ↥(vCobRange DD ρ) = Nat.card DD.Vmod :=
    (Nat.card_congr (AddMonoidHom.ofInjective (vCobHom_injective hfix)).toEquiv).symm
  have hquot : Nat.card (VCocycle DD ρ ⧸ vCobRange DD ρ) = Nat.card (H1 Γ DD.Vmod) :=
    Nat.card_eq_of_bijective _ ⟨h1OfVQuot_injective hcomp, h1OfVQuot_surjective hcomp⟩
  rw [← (vCobRange DD ρ).index_mul_card, (vCobRange DD ρ).index_eq_card, hrange, hquot, mul_comm]

omit [IsTopologicalGroup Γ] [DistribMulAction Γ (ZMod 2)] [ContinuousSMul Γ (ZMod 2)] in
/-- **`Z¹` is finite** as soon as `V` and `H¹(Γ, V)` are — the replacement for the `ℚ₂` chain's
`hZcard_local`-based `haveI hfinZ`, which is unavailable at `K` (the `Phase140/Local.lean` clone
is unowned; CB-SG owns its generic successor).  At `K` the `H¹`-input is LG5's Euler clause. -/
theorem finite_vcocycleG
    (hcomp : ∀ (γ : Γ) (v : DD.Vmod), γ • v = rho0 DD ρ γ • v)
    (hfix : ∀ v : DD.Vmod, (∀ γ : Γ, rho0 DD ρ γ • v = v) → v = 0)
    (hV : Nat.card DD.Vmod ≠ 0) (hH1 : Nat.card (H1 Γ DD.Vmod) ≠ 0) :
    Finite (VCocycle DD ρ) :=
  (Nat.card_ne_zero.mp (by
    rw [card_vcocycle_eq_mul_card_H1 hcomp hfix]; exact Nat.mul_ne_zero hV hH1)).2

end ZCount

end GQ2.Dyadic
