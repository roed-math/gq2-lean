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

/-! ## §3 The form compatibility and the reindexing transport, at a general `Γ`

The two genuinely `G_ℚ₂`-typed declarations of the `ℚ₂` chain, retyped:
`GQ2/GaussZ/Local.lean:172`'s `QZeroBar_eq_Q0loc` (the descended base determinant form **is**
`Q⁰_loc` through the transport `Φ`) and `GQ2/GaussZ/FinalD.lean:60`'s `Q0loc_reindexHom_hom`
(the `MonoidHom`-level `Q⁰` reindexing used to push the head datum down).  Both proofs are the
models' verbatim; only §1's bridge replaces `iotaB_eq_iotaF`. -/

section FormCompatG

variable {Bg : Type} [Group Bg] [Finite Bg] [TopologicalSpace Bg] [DiscreteTopology Bg]
  {D : RadicalCoverData Bg} {DD : DescData D}
variable {Γ : Type} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
  [DistribMulAction Γ (ZMod 2)] [ContinuousSMul Γ (ZMod 2)]
  [DistribMulAction Γ (MuN 2)] [ContinuousSMul Γ (MuN 2)]
variable {ρM : ContinuousMonoidHom Γ (Bg ⧸ D.M)}
variable [TopologicalSpace DD.Vmod] [DiscreteTopology DD.Vmod]
  [DistribMulAction Γ DD.Vmod] [ContinuousSMul Γ DD.Vmod]
variable [TopologicalSpace DD.C0] [DiscreteTopology DD.C0]

omit [IsTopologicalGroup Γ] [DistribMulAction Γ (ZMod 2)] [ContinuousSMul Γ (ZMod 2)]
  [DistribMulAction Γ (MuN 2)] [ContinuousSMul Γ (MuN 2)] [ContinuousSMul Γ DD.Vmod]
  [TopologicalSpace DD.C0] [DiscreteTopology DD.C0] in
/-- `h1OfVQuot` on a class (the `ℚ₂` `h1OfVQuot_mk` is `private`; restated here rather than
editing `GQ2/GaussZ/Local.lean`). -/
private theorem h1OfVQuot_mk' (hcomp : ∀ (γ : Γ) (v : DD.Vmod), γ • v = rho0 DD ρM γ • v)
    (c : VCocycle DD ρM) :
    h1OfVQuot hcomp (QuotientAddGroup.mk c) = H1mk Γ DD.Vmod (toZ1 hcomp c) := rfl

omit [ContinuousSMul Γ DD.Vmod] [DiscreteTopology DD.C0] in
/-- **The form compatibility at a general `Γ`** — the `Γ`-generic
`GQ2.SectionEight.AffineTLift.QZeroBar_eq_Q0loc`: under the transport `Φ = h1OfVQuot`, the
descended base determinant form `Q̄⁰` is LG2's `Q⁰_loc` at the bundle `D`.  §1's
`iotaB_eq_iotaFG` replaces the `ℚ₂` `iotaB_eq_iotaF`, and the `Quotient.out` representative on
the `H¹` side differs from the transported cocycle by a `B¹`-shift, absorbed mod `B²` by the
(already `Γ`-generic) `graphPullback_shift_mem_B2`. -/
theorem QZeroBar_eq_Q0locG (D6 : TateDualityG Γ 2)
    (hcomp : ∀ (γ : Γ) (v : DD.Vmod), γ • v = rho0 DD ρM γ • v)
    (ρc : ContinuousMonoidHom Γ DD.C0) (hρc : ∀ γ, ρc γ = rho0 DD ρM γ)
    (htriv : ∀ (γ : Γ) (m : ZMod 2), γ • m = m)
    (x : VCocycle DD ρM ⧸ vCobRange DD ρM) :
    QZeroBar DD ρM htriv x = Q0loc D6 DD.dat ρc (h1OfVQuot hcomp x) := by
  induction x using QuotientAddGroup.induction_on with
  | H c =>
    rw [QZeroBar_mk, h1OfVQuot_mk']
    -- the `out` representative differs from `toZ1 c` by a `B¹`-element
    have hout : H1mk Γ DD.Vmod (Quotient.out (H1mk Γ DD.Vmod (toZ1 hcomp c)))
        = H1mk Γ DD.Vmod (toZ1 hcomp c) := by
      show Quotient.mk'' (Quotient.out (H1mk Γ DD.Vmod (toZ1 hcomp c)))
        = H1mk Γ DD.Vmod (toZ1 hcomp c)
      exact Quotient.out_eq' _
    rw [H1mk_eq_iff, AddSubgroup.mem_addSubgroupOf] at hout
    obtain ⟨w, hw⟩ := AddMonoidHom.mem_range.mp hout
    have hz₀c : ((Quotient.out (H1mk Γ DD.Vmod (toZ1 hcomp c))
        : ↥(Z1 Γ DD.Vmod)) : Γ → DD.Vmod) = (c + vCob DD ρM w).c := by
      funext γ
      have hγ' : γ • w - w = (Quotient.out (H1mk Γ DD.Vmod (toZ1 hcomp c))
          : ↥(Z1 Γ DD.Vmod)).1 γ - c.c γ := congrFun hw γ
      show (Quotient.out (H1mk Γ DD.Vmod (toZ1 hcomp c))
          : ↥(Z1 Γ DD.Vmod)).1 γ = c.c γ + (rho0 DD ρM γ • w - w)
      rw [← hcomp γ w, hγ']
      abel
    show QZero DD ρM c = iotaF D6 (H2ofFun Γ (graphPullback DD.dat (⇑ρc)
      ((Quotient.out (H1mk Γ DD.Vmod (toZ1 hcomp c)) : ↥(Z1 Γ DD.Vmod)) : _)))
    have hρfun : (⇑ρc : Γ → DD.C0) = fun γ => rho0 DD ρM γ := funext hρc
    rw [hρfun, hz₀c,
      ShapiroLedger.H2ofFun_eq_of_sub_mem_B2 (graphPullback_shift_mem_B2 htriv c w),
      ← iotaB_eq_iotaFG D6 (graphPullback_mem_Z2_of_cocycle htriv c)]
    rfl

end FormCompatG

section ReindexG

variable {Γ : Type} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
  [DistribMulAction Γ (ZMod 2)] [ContinuousSMul Γ (ZMod 2)]
  [DistribMulAction Γ (MuN 2)] [ContinuousSMul Γ (MuN 2)]
variable {C C' : Type} [Group C] [TopologicalSpace C] [DiscreteTopology C] [Finite C]
  [Group C'] [TopologicalSpace C'] [DiscreteTopology C'] [Finite C']
variable {V : Type} [AddCommGroup V] [TopologicalSpace V] [DiscreteTopology V] [Finite V]
  [DistribMulAction Γ V] [ContinuousSMul Γ V]
  [DistribMulAction C V] [DistribMulAction C' V]

omit [DiscreteTopology C] [Finite C] [DiscreteTopology C'] [Finite C'] [Finite V]
  [ContinuousSMul Γ V] in
/-- **`Q⁰` reindexing along a `MonoidHom`-composite at a general `Γ`** — the `Γ`-generic
`GQ2.SectionNine.Q0loc_reindexHom_hom` (`GQ2/GaussZ/FinalD.lean:60`).  Verbatim: the underlying
identity `ShapiroDeepness.graphPullback_reindexHom` is ambient-free. -/
theorem Q0loc_reindexHom_homG (D : TateDualityG Γ 2) (dat : FactorSet C V) (φ : C' →* C)
    (hφ : ∀ (c' : C') (v : V), c' • v = φ c' • v)
    (ρ' : ContinuousMonoidHom Γ C') (ρc : ContinuousMonoidHom Γ C)
    (hρc : ∀ g : Γ, ρc g = φ (ρ' g)) (x : H1 Γ V) :
    Q0loc D (dat.reindexHom ⇑φ) ρ' x = Q0loc D dat ρc x := by
  show iotaF D (H2ofFun Γ (graphPullback (dat.reindexHom ⇑φ) ⇑ρ' (Quotient.out x).1))
    = iotaF D (H2ofFun Γ (graphPullback dat ⇑ρc (Quotient.out x).1))
  rw [ShapiroDeepness.graphPullback_reindexHom dat ⇑φ hφ ⇑ρ' (Quotient.out x).1,
    show (⇑φ ∘ ⇑ρ') = ⇑ρc from funext fun g => (hρc g).symm]

end ReindexG

/-! ## §4 The pinned Gauss value on `H¹(G_K, V)` — LG5, in signed form

`GQ2/GaussZ/Local.lean` §(D)/(E) turns `prop_6_18`'s zero count into the signed sum
`∑ᶠ sign(Q⁰_loc) = ∓2^m`.  Here the same conversion runs off LG5's
`local_gauss_K_zeroCount_{add,sub}`, giving the packet eq. (115) values

  `∑ᶠ_{H¹(G_K,V)} sign(Q⁰) = (−1)^n · 2^{nm}` (unramified marking),  `= +2^{nm}` (ramified),

`n = [K : ℚ₂]`.  **Degree-shift audit, row 3**: the `ℚ₂` constants `∓2^m` are the `n = 1` case of
these, and the `(−1)^n` in the unramified head is *not* a sign convention — it is the parity
split inside `local_gauss_K` (`arf = n mod 2` when unramified), which is why the unramified
theorem below case-splits on `Even P.n` while the ramified one does not. -/

section PinnedK

variable {C : Type} [Group C] [TopologicalSpace C] [DiscreteTopology C] [Finite C]

section SignedSum

variable {Γ : Type} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
  [DistribMulAction Γ (ZMod 2)] [ContinuousSMul Γ (ZMod 2)]
  [DistribMulAction Γ (MuN 2)] [ContinuousSMul Γ (MuN 2)]
variable {V : Type} [AddCommGroup V] [TopologicalSpace V] [DiscreteTopology V] [Finite V]
  [DistribMulAction Γ V] [ContinuousSMul Γ V] [DistribMulAction C V]

omit [DiscreteTopology C] [Finite C] [Finite V] [ContinuousSMul Γ V] in
/-- **The signed-sum extraction at a general `Γ`** — the `Γ`-generic
`GQ2.SectionEight.AffineTLift.finsum_sign_eq`: with the zero count of `Q⁰` and
`#H¹(Γ, V) = 2^{2M}` known, `∑ᶠ sign(Q⁰) = 2·zc − 2^{2M}`.  The `ℚ₂` version got its `Finite H¹`
from `Foundations.finite_H1`; here it comes from the count itself. -/
theorem finsum_sign_eqG (D : TateDualityG Γ 2) (dat : FactorSet C V)
    (ρ : ContinuousMonoidHom Γ C)
    (zc : ℕ) (hzc : QuadraticFp2.zeroCount (Q0loc D dat ρ (V := V)) = zc)
    {M : ℕ} (hH1 : Nat.card (H1 Γ V) = 2 ^ (2 * M)) :
    ∑ᶠ y : H1 Γ V, sign (Q0loc D dat ρ y) = 2 * (zc : ℤ) - 2 ^ (2 * M) := by
  classical
  haveI : Finite (H1 Γ V) := (Nat.card_ne_zero.mp (by rw [hH1]; positivity)).2
  haveI : Fintype (H1 Γ V) := Fintype.ofFinite _
  rw [finsum_eq_sum_of_fintype]
  -- bridge the two `sign`s (`SectionEight.sign` in the residue, `QuadraticFp2.sign` in
  -- `gaussSum`), then evaluate through `gaussSum_eq`
  have hsign : ∀ s : ZMod 2, sign s = QuadraticFp2.sign s := by decide
  calc (∑ y : H1 Γ V, sign (Q0loc D dat ρ y))
      = ∑ y : H1 Γ V, QuadraticFp2.sign (Q0loc D dat ρ y) :=
        Finset.sum_congr rfl fun y _ => hsign _
    _ = 2 * (zc : ℤ) - 2 ^ (2 * M) := by
        have hge := QuadraticFp2.gaussSum_eq (V := H1 Γ V) (Q0loc D dat ρ)
        unfold QuadraticFp2.gaussSum at hge
        rw [hge, hzc, ← Nat.card_eq_fintype_card, hH1]
        push_cast
        ring

end SignedSum

section AtK

variable (P : FieldParameters) (U : Subgroup AbsGalQ2)
variable {V : Type} [AddCommGroup V] [TopologicalSpace V] [DiscreteTopology V] [Finite V]

/-- **Packet eq. (115), unramified head, signed** — `∑ᶠ sign(Q⁰_{K,V}) = (−1)^n · 2^{nm}`.

LG5's dichotomy in one line: in *odd* degree the marking's Arf invariant is `1`
(`local_gauss_K_zeroCount_sub`) and the sum is `−2^{nm}`; in *even* degree it is `0`
(`local_gauss_K_zeroCount_add`, whose `hplus` is satisfied by the parity alone) and the sum is
`+2^{nm}`.  Together: `(−1)^n 2^{nm}`, which is `SourceNumerics.gaussUnram` at
`standardNumerics n` on the nose (`gaussUnram_standard`). -/
theorem sum_sign_Q0loc_K_unramified
    (hU : IsOpen (U : Set AbsGalQ2)) [Finite (AbsGalQ2 ⧸ U)] (hn : U.index = P.n)
    [DistribMulAction ↥U (ZMod 2)] [ContinuousSMul ↥U (ZMod 2)]
    [DistribMulAction ↥U (MuN 2)] [ContinuousSMul ↥U (MuN 2)]
    [DistribMulAction ↥U V] [ContinuousSMul ↥U V] [DistribMulAction C V]
    (D : TateDualityG ↥U 2)
    (tameFK : ContinuousMonoidHom ↥U (Tq P.qK)) (htameFK : Function.Surjective ⇑tameFK)
    (c : ContinuousMonoidHom (Tq P.qK) C) (hc : Function.Surjective ⇑c)
    (ρ : ContinuousMonoidHom ↥U C) (hfac : ∀ g, ρ g = c (tameFK g))
    (hρ : ∀ (g : ↥U) (v : V), g • v = ρ g • v)
    (hfaith : ∀ h : C, (∀ v : V, h • v = v) → h = 1)
    (hsimple : ∀ W : AddSubgroup V, (∀ (h : C), ∀ w ∈ W, h • w ∈ W) → W = ⊥ ∨ W = ⊤)
    (q : V → ZMod 2) (hq : QuadraticFp2.IsQuadraticFp2 q) (hns : QuadraticFp2.Nonsingular q)
    (hinv : QuadraticFp2.IsInvariant C q)
    (dat : FactorSet C V) (hdat : IsEquivariantFactorSet q dat)
    (m : ℕ) (hm : 1 ≤ m) (hcard : Nat.card V = 2 ^ (2 * m))
    (hunram : ∀ v : V, c (tqTau P.qK) • v = v) :
    ∑ᶠ y : H1 ↥U V, sign (Q0loc D dat ρ y) = (-1 : ℤ) ^ P.n * 2 ^ (P.n * m) := by
  classical
  have hnr : ¬∃ v : V, c (tqTau P.qK) • v ≠ v := fun h => h.elim fun v hv => hv (hunram v)
  have hH1 : Nat.card (H1 ↥U V) = 2 ^ (2 * (m * P.n)) :=
    card_H1_eq_of_markingK P U hU hn D tameFK htameFK c hc ρ hfac hρ hsimple q hq hns hinv
      m hm hcard
  have hM : 1 ≤ m * P.n :=
    Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by have := P.one_le_n; omega))
  have hle : (2 : ℕ) ^ (m * P.n - 1) ≤ 2 ^ (2 * (m * P.n) - 1) :=
    Nat.pow_le_pow_right (by norm_num) (by omega)
  have e1 : (2 : ℤ) ^ (2 * (m * P.n)) = 2 * 2 ^ (2 * (m * P.n) - 1) := by
    rw [← pow_succ']; congr 1; omega
  have e2 : (2 : ℤ) ^ (m * P.n) = 2 * 2 ^ (m * P.n - 1) := by rw [← pow_succ']; congr 1; omega
  have hmn : (2 : ℤ) ^ (P.n * m) = 2 ^ (m * P.n) := by rw [mul_comm]
  rcases Nat.even_or_odd P.n with hev | hodd
  · -- even degree: the Arf invariant vanishes, the sum is `+2^{nm}`
    have hzc : QuadraticFp2.zeroCount (Q0loc D dat ρ (V := V))
        = 2 ^ (2 * m * P.n - 1) + 2 ^ (m * P.n - 1) :=
      local_gauss_K_zeroCount_add P U hU hn D tameFK htameFK c hc ρ hfac hρ hfaith hsimple
        q hq hns hinv dat hdat m hm hcard (fun h => absurd h hnr) (Or.inr hev)
    rw [finsum_sign_eqG D dat ρ _ (by rw [hzc, mul_assoc]) hH1, hev.neg_one_pow, one_mul, hmn]
    push_cast
    linarith [e1, e2]
  · -- odd degree: the Arf invariant is `1`, the sum is `−2^{nm}`
    have hzc : QuadraticFp2.zeroCount (Q0loc D dat ρ (V := V))
        = 2 ^ (2 * m * P.n - 1) - 2 ^ (m * P.n - 1) :=
      local_gauss_K_zeroCount_sub P U hU hn D tameFK htameFK c hc ρ hfac hρ hfaith hsimple
        q hq hns hinv dat hdat m hm hcard hunram hodd
    rw [finsum_sign_eqG D dat ρ _ (by rw [hzc, mul_assoc]) hH1, hodd.neg_one_pow, hmn]
    push_cast [Nat.cast_sub hle]
    linarith [e1, e2]

/-- **Packet eq. (115), ramified head, signed** — `∑ᶠ sign(Q⁰_{K,V}) = +2^{nm}` at *every*
degree (`local_gauss_K`'s ramified branch has no parity condition).  This is
`SourceNumerics.gaussRam` at `standardNumerics n` (`gaussRam_standard`). -/
theorem sum_sign_Q0loc_K_ramified
    (hU : IsOpen (U : Set AbsGalQ2)) [Finite (AbsGalQ2 ⧸ U)] (hn : U.index = P.n)
    [DistribMulAction ↥U (ZMod 2)] [ContinuousSMul ↥U (ZMod 2)]
    [DistribMulAction ↥U (MuN 2)] [ContinuousSMul ↥U (MuN 2)]
    [DistribMulAction ↥U V] [ContinuousSMul ↥U V] [DistribMulAction C V]
    (D : TateDualityG ↥U 2)
    (tameFK : ContinuousMonoidHom ↥U (Tq P.qK)) (htameFK : Function.Surjective ⇑tameFK)
    (c : ContinuousMonoidHom (Tq P.qK) C) (hc : Function.Surjective ⇑c)
    (ρ : ContinuousMonoidHom ↥U C) (hfac : ∀ g, ρ g = c (tameFK g))
    (hρ : ∀ (g : ↥U) (v : V), g • v = ρ g • v)
    (hfaith : ∀ h : C, (∀ v : V, h • v = v) → h = 1)
    (hsimple : ∀ W : AddSubgroup V, (∀ (h : C), ∀ w ∈ W, h • w ∈ W) → W = ⊥ ∨ W = ⊤)
    (q : V → ZMod 2) (hq : QuadraticFp2.IsQuadraticFp2 q) (hns : QuadraticFp2.Nonsingular q)
    (hinv : QuadraticFp2.IsInvariant C q)
    (dat : FactorSet C V) (hdat : IsEquivariantFactorSet q dat)
    (m : ℕ) (hm : 1 ≤ m) (hcard : Nat.card V = 2 ^ (2 * m))
    (hram : ∃ v : V, c (tqTau P.qK) • v ≠ v)
    (hcert : Nonempty (RamifiedCertificate P U V c ρ)) :
    ∑ᶠ y : H1 ↥U V, sign (Q0loc D dat ρ y) = (2 : ℤ) ^ (P.n * m) := by
  classical
  have hH1 : Nat.card (H1 ↥U V) = 2 ^ (2 * (m * P.n)) :=
    card_H1_eq_of_markingK P U hU hn D tameFK htameFK c hc ρ hfac hρ hsimple q hq hns hinv
      m hm hcard
  have hzc : QuadraticFp2.zeroCount (Q0loc D dat ρ (V := V))
      = 2 ^ (2 * m * P.n - 1) + 2 ^ (m * P.n - 1) :=
    local_gauss_K_zeroCount_add P U hU hn D tameFK htameFK c hc ρ hfac hρ hfaith hsimple
      q hq hns hinv dat hdat m hm hcard (fun _ => hcert) (Or.inl hram)
  have hM : 1 ≤ m * P.n :=
    Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by have := P.one_le_n; omega))
  have e1 : (2 : ℤ) ^ (2 * (m * P.n)) = 2 * 2 ^ (2 * (m * P.n) - 1) := by
    rw [← pow_succ']; congr 1; omega
  have e2 : (2 : ℤ) ^ (m * P.n) = 2 * 2 ^ (m * P.n - 1) := by rw [← pow_succ']; congr 1; omega
  rw [finsum_sign_eqG D dat ρ _ (by rw [hzc, mul_assoc]) hH1,
    show P.n * m = m * P.n from mul_comm _ _]
  push_cast
  linarith [e1, e2]

end AtK

end PinnedK

/-! ## §5 The `standardNumerics` pins

The two Gauss values of `standardNumerics n` are exactly §4's, and `h1Mult` is exactly §2's.
Recorded so that the degree-shift audit is checkable by `#check`, not by reading prose. -/

/-- `standardNumerics n`'s unramified Gauss value **is** `(−1)^n 2^{nm}` — `rfl`. -/
theorem gaussUnram_standard (n m : ℕ) :
    (standardNumerics n).gaussUnram m = (-1 : ℤ) ^ n * 2 ^ (n * m) := rfl

/-- `standardNumerics n`'s ramified Gauss value **is** `2^{nm}` — `rfl`. -/
theorem gaussRam_standard (n m : ℕ) : (standardNumerics n).gaussRam m = (2 : ℤ) ^ (n * m) := rfl

/-- `standardNumerics n`'s `h1Mult` **is** `#H¹(G_K, V)` as a function of `#V` at the modules the
Gauss lane sees: `#V = 2^{2m}` and `#H¹ = 2^{2mn} = (#V)^n` (LG5's Euler clause).  This is the
numerical form of §2's finding, and the reason `h1Mult V = V^n` — not `V^2` — is the correct
`SourceNumerics` leaf. -/
theorem h1Mult_standard_of_card (n m : ℕ) :
    (standardNumerics n).h1Mult (2 ^ (2 * m)) = 2 ^ (2 * (m * n)) := by
  show (2 ^ (2 * m)) ^ n = 2 ^ (2 * (m * n))
  rw [← pow_mul]
  congr 1
  ring

/-! ## §6 The `GaussZResidueK` twins at the head-inflated enrichment

The `K`-clone of `GQ2/GaussZ/FinalD.lean`'s `gaussZResidueD_local_{un,}ramified`, at SD-R1's
`blockEnrichmentDK`.  Structure identical to the model:

* the boundary equation's head component (`boundaryLift_headK`, SD-R1's *source-generic*
  replacement for the model's two twins) tame-factors every lift through the **fixed**
  `cF = mk'(headActKer) ∘ F.alpha`, so no per-lift `hpack` is needed;
* `gaussZ_reduction` peels off the outer `#V = #B¹` — the non-mover of the degree-shift audit;
* the transport `h1OfVQuot` + §3's `QZeroBar_eq_Q0locG` + §3's `Q0loc_reindexHom_homG` moves the
  sum onto `(H¹(G_K, V), Q⁰_loc)` at the head datum `blockDatHVK`;
* §4 pins the value, from LG5.

The one structural change: `Finite Z¹` comes from §2 rather than from a `#Z¹ = #V²` count, so
this file does **not** depend on a `K`-clone of `GQ2/Phase140/Local.lean`. -/

section HeadInflated

variable {H E : Type} [Group H] [TopologicalSpace H] [DiscreteTopology H] [Finite H]
  [CommGroup E] [TopologicalSpace E] [DiscreteTopology E] [Finite E]
variable {Y : Type} [Group Y] [TopologicalSpace Y] [DiscreteTopology Y] [Finite Y]
variable (T : MarkedTarget H E Y) (Blk : SectionSeven.MinimalBlock T.LY)
variable [Blk.frattiniK.Normal] [(Blk.S.subgroupOf Blk.P).Normal] [Blk.K.Normal]
variable {q : ℕ} {PG : ProfiniteGrp}

/-- **The fixed tame surjection into the faithful head quotient at the `K`-boundary**
(`cF := mk'(headActKer) ∘ F.alpha`) — the `K`-clone of `GQ2.SectionNine.headTameSurj`
(`GQ2/GaussZ/FinalD.lean:83`), retyped from `Ttame` to F3's `Tq q`. -/
noncomputable def headTameSurjK (F : BoundaryFrameK q PG H E) :
    letI : TopologicalSpace (SectionNine.HVq T Blk) := ⊥
    ContinuousMonoidHom (Tq q) (SectionNine.HVq T Blk) :=
  letI : TopologicalSpace (SectionNine.HVq T Blk) := ⊥
  ⟨(QuotientGroup.mk' (SectionNine.headActKer T Blk)).comp F.alpha.toMonoidHom,
    (continuous_of_discreteTopology
      (f := fun hh : H => QuotientGroup.mk' (SectionNine.headActKer T Blk) hh)).comp
      F.alpha.continuous_toFun⟩

omit [TopologicalSpace Y] [DiscreteTopology Y] [Blk.frattiniK.Normal] in
/-- `headTameSurjK` is surjective (`mk'` after the surjective `F.alpha`). -/
theorem headTameSurjK_surjective (F : BoundaryFrameK q PG H E) :
    Function.Surjective ⇑(headTameSurjK T Blk F) :=
  (QuotientGroup.mk'_surjective _).comp F.alpha_surjective

section Twins

variable (FP : FieldParameters) (U : Subgroup AbsGalQ2)
variable {nuP : ContinuousMonoidHom PG Ztwo}

-- `hVne` is unused: `local_gauss_K` derives the mover from `hcard`/`hm`, where the `ℚ₂`
-- `prop_6_18_unramified` took `∃ v ≠ 0` as an input.  The binder is kept for parity with the
-- `AffineDeterminantCertificate` clause this theorem discharges.
set_option linter.unusedVariables false in
/-- **`hGaussZ` at the head-inflated `K`-enrichment, unramified case** — the `K`-clone of
`GQ2.SectionNine.gaussZResidueD_local_unramified`, at the degree-`n` value
`(−1)^n · 2^{nm}` (= `SourceNumerics.gaussUnram m` at `standardNumerics n`).

`b` is any boundary map whose tame coordinate is `tameF_K` (`hbtame`); at the certificate's
`b = sourceBoundaryMapK tame pro2 compat` that hypothesis is `rfl`.  No per-lift tame package:
the dichotomy is the head-level `F.alpha (τ_q)`-triviality, uniform in `ρ`. -/
theorem gaussZResidueDK_unramified
    (hU : IsOpen (U : Set AbsGalQ2)) [Finite (AbsGalQ2 ⧸ U)] (hn : U.index = FP.n)
    [DistribMulAction ↥U (ZMod 2)] [ContinuousSMul ↥U (ZMod 2)]
    [DistribMulAction ↥U (MuN 2)] [ContinuousSMul ↥U (MuN 2)]
    [CompactSpace ↥U] [TotallyDisconnectedSpace ↥U]
    (D : TateDualityG ↥U 2)
    (hE2 : ∀ e : E, e ^ 2 = 1) (hq0 : FP.qK ≠ 0) (hqe : Even FP.qK)
    (F : BoundaryFrameK FP.qK PG H E)
    (tameFK : ContinuousMonoidHom ↥U (Tq FP.qK)) (htameFK : Function.Surjective ⇑tameFK)
    (b : ContinuousMonoidHom ↥U ↥(boundarySubgroupQ FP.qK nuP))
    (hbtame : ∀ g : ↥U, (b g).val.1 = tameFK g)
    (hsimple : ∀ W : AddSubgroup (blockEnrichmentDK T Blk hE2 hq0 hqe F).Vmod,
      (∀ g : (SectionNine.blockFrame T Blk hE2).YC, ∀ w ∈ W, g • w ∈ W) → W = ⊥ ∨ W = ⊤)
    (hVne : ∃ v : (blockEnrichmentDK T Blk hE2 hq0 hqe F).Vmod, v ≠ 0)
    (hnt : ∃ (g : (SectionNine.blockFrame T Blk hE2).YC)
      (v : (blockEnrichmentDK T Blk hE2 hq0 hqe F).Vmod), g • v ≠ v)
    (m : ℕ) (hm : 1 ≤ m)
    (hcard : Nat.card (blockEnrichmentDK T Blk hE2 hq0 hqe F).Vmod = 2 ^ (2 * m))
    (l : (SectionNine.blockFrame T Blk hE2).DR)
    (h : l ≠ (SectionNine.blockFrame T Blk hE2).zeroDR)
    (hunram :
      letI := blockPS_commGroup Blk
      letI := SectionNine.headAct T Blk
      ∀ v : Additive (↥Blk.P ⧸ Blk.S.subgroupOf Blk.P), F.alpha (tqTau FP.qK) • v = v) :
    GaussZResidueK b F (blockEnrichmentDK T Blk hE2 hq0 hqe F) l h
      ((-1 : ℤ) ^ FP.n * 2 ^ (FP.n * m)) := by
  classical
  letI := blockPS_commGroup Blk
  letI := blockActVY Blk
  letI := blockActV Blk
  letI := SectionNine.headAct T Blk
  letI := SectionNine.hvAct T Blk
  letI : TopologicalSpace (SectionNine.HVq T Blk) := ⊥
  haveI : DiscreteTopology (SectionNine.HVq T Blk) := ⟨rfl⟩
  have hl' : l.1 ≠ Blk.frattiniK := fun heq => h (Subtype.ext heq)
  set EnD := blockEnrichmentDK T Blk hE2 hq0 hqe F with hEnDdef
  intro ρ
  set ρM := rhoPrimeK (SectionNine.blockFrame T Blk hE2) b F (EnD.radData l h) rfl ρ with hρMdef
  -- the fixed tame surjection into the faithful head quotient, and the per-`ρ` composite
  set cF : ContinuousMonoidHom (Tq FP.qK) (SectionNine.HVq T Blk) := headTameSurjK T Blk F
    with hcFdef
  have hcF : Function.Surjective ⇑cF := headTameSurjK_surjective T Blk F
  set ρHV : ContinuousMonoidHom ↥U (SectionNine.HVq T Blk) :=
    ⟨(SectionNine.blockProjF T Blk).comp ρ.1.1.toMonoidHom,
      (continuous_of_discreteTopology
        (f := fun c : (SectionNine.blockFrame T Blk hE2).YC => SectionNine.blockProjF T Blk c)).comp
        ρ.1.1.continuous_toFun⟩ with hρHVdef
  have hfacHV : ∀ g : ↥U, ρHV g = cF (tameFK g) := fun g => by
    rw [← hbtame g]
    exact congrArg (⇑(QuotientGroup.mk' (SectionNine.headActKer T Blk)))
      (boundaryLift_headK T Blk hE2 b F ρ g)
  -- the module structure on `V` through the head-quotient composite
  letI instT : TopologicalSpace (Additive (↥Blk.P ⧸ Blk.S.subgroupOf Blk.P)) := ⊥
  haveI instD : DiscreteTopology (Additive (↥Blk.P ⧸ Blk.S.subgroupOf Blk.P)) := ⟨rfl⟩
  letI instA : DistribMulAction ↥U (Additive (↥Blk.P ⧸ Blk.S.subgroupOf Blk.P)) :=
    DistribMulAction.compHom _ ρHV.toMonoidHom
  haveI instC : ContinuousSMul ↥U (Additive (↥Blk.P ⧸ Blk.S.subgroupOf Blk.P)) := ⟨by
    show Continuous fun p : ↥U × Additive (↥Blk.P ⧸ Blk.S.subgroupOf Blk.P) => ρHV p.1 • p.2
    exact (continuous_of_discreteTopology
        (f := fun z : SectionNine.HVq T Blk × Additive (↥Blk.P ⧸ Blk.S.subgroupOf Blk.P) =>
          z.1 • z.2)).comp
      ((ρHV.continuous.comp continuous_fst).prodMk continuous_snd)⟩
  -- the same instances re-keyed at the syntactic projections
  letI : TopologicalSpace EnD.Vmod := instT
  haveI : DiscreteTopology EnD.Vmod := instD
  letI : DistribMulAction ↥U EnD.Vmod := instA
  haveI : ContinuousSMul ↥U EnD.Vmod := instC
  letI : TopologicalSpace (EnD.descData l h).Vmod := instT
  haveI : DiscreteTopology (EnD.descData l h).Vmod := instD
  letI : DistribMulAction ↥U (EnD.descData l h).Vmod := instA
  haveI : ContinuousSMul ↥U (EnD.descData l h).Vmod := instC
  letI : DistribMulAction (SectionNine.HVq T Blk) EnD.Vmod := SectionNine.hvAct T Blk
  letI : DistribMulAction (SectionNine.HVq T Blk) (EnD.descData l h).Vmod :=
    SectionNine.hvAct T Blk
  letI : TopologicalSpace (EnD.descData l h).C0 :=
    (inferInstance : TopologicalSpace (SectionNine.blockFrame T Blk hE2).YC)
  haveI : DiscreteTopology (EnD.descData l h).C0 :=
    (inferInstance : DiscreteTopology (SectionNine.blockFrame T Blk hE2).YC)
  haveI : Finite (EnD.descData l h).C0 :=
    (inferInstance : Finite (SectionNine.blockFrame T Blk hE2).YC)
  -- spelling covers: shadow the global quotient-topology at the raw `Y ⧸ K` spelling with
  -- the frame's instances, and provide the `YC`-spelled action on the raw module
  letI : TopologicalSpace (Y ⧸ Blk.K) :=
    (inferInstance : TopologicalSpace (SectionNine.blockFrame T Blk hE2).YC)
  haveI : DiscreteTopology (Y ⧸ Blk.K) :=
    (inferInstance : DiscreteTopology (SectionNine.blockFrame T Blk hE2).YC)
  haveI : Finite (Y ⧸ Blk.K) := (inferInstance : Finite (SectionNine.blockFrame T Blk hE2).YC)
  letI : DistribMulAction ((SectionNine.blockFrame T Blk hE2).YC)
      (Additive (↥Blk.P ⧸ Blk.S.subgroupOf Blk.P)) := blockActV Blk
  letI : DistribMulAction ((SectionNine.blockFrame T Blk hE2).YC) (EnD.descData l h).Vmod :=
    blockActV Blk
  -- the roundtrip and the bridge
  have hround : ∀ γ : ↥U, rho0 (EnD.descData l h) ρM γ = ρ.1.1 γ :=
    rho0_descData_rhoPrimeK b F EnD l h ρ
  have hcomp : ∀ (γ : ↥U) (v : (EnD.descData l h).Vmod),
      γ • v = rho0 (EnD.descData l h) ρM γ • v := by
    intro γ v
    rw [show rho0 (EnD.descData l h) ρM γ • v
        = SectionNine.blockProjF T Blk (rho0 (EnD.descData l h) ρM γ) • v from
      SectionNine.blockProjF_compat T Blk _ v, hround γ]
    rfl
  -- the `V^{C₀} = 0` freeness input (hfaith-free)
  have hsurjρ' : Function.Surjective (fun γ : ↥U => rho0 (EnD.descData l h) ρM γ) :=
    fun y => by
      obtain ⟨γ, hγ⟩ := ρ.1.2 y
      exact ⟨γ, (hround γ).trans hγ⟩
  have hfix : ∀ v : (EnD.descData l h).Vmod,
      (∀ γ : ↥U, rho0 (EnD.descData l h) ρM γ • v = v) → v = 0 :=
    hfix_of_simple_nt hsurjρ' hsimple hnt
  -- the pinned value at the faithful head quotient (LG5, §4)
  have hunramF : ∀ v : Additive (↥Blk.P ⧸ Blk.S.subgroupOf Blk.P), cF (tqTau FP.qK) • v = v :=
    hunram
  have hpinned := sum_sign_Q0loc_K_unramified FP U hU hn D tameFK htameFK cF hcF ρHV hfacHV
    (fun _ _ => rfl) (SectionNine.hvAct_faithful T Blk) (SectionNine.hv_simple T Blk)
    (blockQbarK T Blk hq0 hqe F.alpha F.alpha_surjective l hl')
    (blockHquadK T Blk hq0 hqe F.alpha F.alpha_surjective l hl')
    (blockHnsK T Blk hq0 hqe F.alpha F.alpha_surjective l hl')
    (hv_invK T Blk hq0 hqe F l hl') (blockDatHVK T Blk hq0 hqe F l hl')
    (blockDatHV_specK T Blk hq0 hqe F l hl') m hm hcard hunramF
  -- `Z¹` is finite, from §2 and the Euler clause (no `#Z¹ = #V²` count needed)
  have hH1c : Nat.card (H1 ↥U (EnD.descData l h).Vmod) = 2 ^ (2 * (m * FP.n)) :=
    card_H1_eq_of_markingK FP U hU hn D tameFK htameFK cF hcF ρHV hfacHV (fun _ _ => rfl)
      (SectionNine.hv_simple T Blk)
      (blockQbarK T Blk hq0 hqe F.alpha F.alpha_surjective l hl')
      (blockHquadK T Blk hq0 hqe F.alpha F.alpha_surjective l hl')
      (blockHnsK T Blk hq0 hqe F.alpha F.alpha_surjective l hl')
      (hv_invK T Blk hq0 hqe F l hl') m hm hcard
  haveI hfinZ : Finite (VCocycle (EnD.descData l h) ρM) :=
    finite_vcocycleG hcomp hfix Nat.card_pos.ne' (by rw [hH1c]; positivity)
  -- the transport bijection `Z¹⧸B¹ ≅ H¹`
  have hbij : Function.Bijective (h1OfVQuot hcomp) :=
    ⟨h1OfVQuot_injective hcomp, h1OfVQuot_surjective hcomp⟩
  have hQbar : ∑ᶠ x, SectionEight.sign (QZeroBar (EnD.descData l h) ρM smul_zmodTwo x)
      = (-1 : ℤ) ^ FP.n * 2 ^ (FP.n * m) := by
    rw [← hpinned]
    refine finsum_eq_of_bijective (h1OfVQuot hcomp) hbij fun x => ?_
    rw [QZeroBar_eq_Q0locG D hcomp ρ.1.1 (fun γ => (hround γ).symm) smul_zmodTwo x]
    exact congrArg SectionEight.sign
      (Q0loc_reindexHom_homG (C := SectionNine.HVq T Blk)
        (C' := (SectionNine.blockFrame T Blk hE2).YC) D
        (blockDatHVK T Blk hq0 hqe F l hl') (SectionNine.blockProjF T Blk)
        (SectionNine.blockProjF_compat T Blk) ρ.1.1 ρHV (fun g => rfl) (h1OfVQuot hcomp x))
  calc ∑ᶠ cc : VCocycle (EnD.descData l h) ρM,
        SectionEight.sign (QZero (EnD.descData l h) ρM cc)
      = (Nat.card EnD.Vmod : ℤ)
          * ∑ᶠ x, SectionEight.sign (QZeroBar (EnD.descData l h) ρM smul_zmodTwo x) :=
        gaussZ_reduction smul_zmodTwo hfix
    _ = (Nat.card EnD.Vmod : ℤ) * ((-1 : ℤ) ^ FP.n * 2 ^ (FP.n * m)) := by rw [hQbar]

end Twins

end HeadInflated

end GQ2.Dyadic
