/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Opus-4.8 and Fable-5
-/
import GQ2.VLiftCount

/-!
# The master count at a parameterized `#H¹` multiplicity (dyadic campaign, ticket SD-R3)

The **`vH`-wrapper** of `GQ2.SectionEight.AffineTLift.two_mul_card_centralImage`
(`GQ2/VLiftCount.lean:764-816`), ruled into SD-R3 by owner question Q1 (memo §4.3's "price one
file"): its sole consumer is `GQ2/Phase140/Assembly.lean:191`, and the (c) parameterization of
memo §4.1 replaces the **inner** `|V|` of `hZcard` by the record's `SN.h1Mult |V|`.

## This file is NOT a boundary clone

`VLiftCount.lean` is 0/830 `b`-dense — it is below the boundary and is reused untouched by every
other part-III file.  What moves here is purely *numeric*: one hypothesis (`hZcard`) and one
slot of the conclusion.  No `boundarySubgroupQ`, no `BoundaryFrameK`, no `q`/`P`/`nuP`.

## Finding: the "thin wrapper" is not thin — a 4-deep `private` chain

Memo §4.3 budgeted this as "a thin generic wrapper".  Measured: `hZcard` and `hGaussZ` do enter
only in the model's terminal `rw [...]; ring` (`:812-816`), exactly as §4.1(c) predicted — **but
every intermediate step is `private`**:

    sum_sign_betaChi_eq_ite            (:619, private)
      → doubleSum_eq_two_mul_card_liftable   (:645, private)
    sum_sum_sign_betaChi_eq_card       (:676, private)
    sum_sum_sign_betaChi_add_betaXi_eq (:726, private)

so the pre-`hZcard` identity is not reachable from outside the model file and the chain must be
copied.  Measured cost: 4 helpers, ~130 ln, all verbatim.  Recorded as a budget correction (this
is the private-helper tax SD-R2 flagged, larger here than its ~10% rule of thumb).

To keep the copy paying for itself the chain is re-exported once, `hZcard`-free, as
`masterCountRaw`; both the model's shape and the parameterized shape are three-line corollaries
of it.  `masterCountRaw` is the reusable artifact — if a future lane needs a third normalization
it costs nothing.

## Parameterization delta versus the `ℚ₂` model

| | model (`:780-786`) | here |
|---|---|---|
| `hZcard` | `#Z¹(V) = #V * #V` | `#Z¹(V) = #V * vH` |
| conclusion | `#V * (#V + G0 * Σ)` | `#V * (vH + G0 * Σ)` |

Nothing else moves; `hGaussZ`'s `#V` is the **outer** `#B¹` factor and is degree-independent
(memo §1.3).  `two_mul_card_centralImageN_eq` is the `vH := #V` regression: it reproduces the
model's statement on the nose.

Plain-import (memo §5).

Axioms: none beyond std-3.  Print check performed for every declaration in this file: each
prints `[propext, Classical.choice, Quot.sound]`, equal to its model's print — hence a subset.
-/

namespace GQ2.Dyadic

open GQ2 GQ2.SectionEight GQ2.SectionEight.AffineTLift
open CentralObstruction ContCoh

/-! `QuadraticFp2` is deliberately **not** opened: it exports a second `sign`
(`GQ2/GaussCount/Wall.lean:35`, `if a = 0 then 1 else -1`) distinct from the `SectionEight.sign`
(`GQ2/SectionEight/Fourier.lean:38`, `(-1) ^ s.val`) that the model uses.  The model resolves the
clash through its enclosing `namespace GQ2.SectionEight`; a clone in `GQ2.Dyadic` has no such
tiebreak, so the ambiguity must be removed at the `open`.  Purely a name-resolution matter — the
`sign` below is the model's on the nose. -/

variable {Bg : Type} [Group Bg] [Finite Bg] [TopologicalSpace Bg] [DiscreteTopology Bg]
  {D : RadicalCoverData Bg}
variable {Γ : Type} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
  [DistribMulAction Γ (ZMod 2)]
variable {DD : DescData D} {σ : DD.C0 →* Bg ⧸ D.T}
  {ρ : ContinuousMonoidHom Γ (Bg ⧸ D.M)}

/-! ## The copied `private` chain

Verbatim copies of `GQ2/VLiftCount.lean`'s four `private` helpers (`:619`, `:645`, `:676`,
`:726`).  They are re-`private` here: nothing outside this file should see them — the public
surface is `masterCountRaw` and the two corollaries. -/

open scoped Classical in
/-- **Step 1** of the master count.  Verbatim copy of `sum_sign_betaChi_eq_ite`
(`GQ2/VLiftCount.lean:619`); see this file's header for why the copy is unavoidable. -/
private theorem sum_sign_betaChi_eq_iteN [Fintype ↥(TCharC D)]
    (S : CountSections DD σ) (hσ : ∀ cc : DD.C0, piQbar DD (σ cc) = cc)
    (htriv : ∀ (γ : Γ) (m : ZMod 2), γ • m = m)
    (hH2 : Nat.card (H2 Γ (ZMod 2)) = 2)
    (hsep : ∀ c : VCocycle DD ρ, (∀ χ : ↥(TCharC D), betaChi S hσ χ c = 0) → TLiftable hσ c)
    (c : VCocycle DD ρ) :
    (∑ χ : ↥(TCharC D), sign (betaChi S hσ χ c))
      = if TLiftable hσ c then (Nat.card ↥(TCharC D) : ℤ) else 0 := by
  classical
  by_cases hc : TLiftable hσ c
  · rw [if_pos hc]
    rw [Finset.sum_congr rfl fun χ _ => by
      rw [betaChi_of_tliftable S hσ htriv hc χ, sign_zero]]
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one,
      Nat.card_eq_fintype_card]
  · rw [if_neg hc]
    have hnz : ¬∀ χ : ↥(TCharC D), betaChi S hσ χ c = 0 := fun hall => hc (hsep c hall)
    have hadd : ∀ χ ψ : ↥(TCharC D),
        betaChi S hσ (χ + ψ) c = betaChi S hσ χ c + betaChi S hσ ψ c :=
      fun χ ψ => betaChi_add_char S hσ htriv hH2 χ ψ c
    have := sum_sign_eq_zero (fun χ : ↥(TCharC D) => betaChi S hσ χ c) hadd hnz
    rwa [finsum_eq_sum_of_fintype] at this

open scoped Classical in
/-- **Way 1** of the master double sum.  Verbatim copy of
`doubleSum_eq_two_mul_card_liftable` (`GQ2/VLiftCount.lean:645`). -/
private theorem doubleSum_eq_two_mul_card_liftableN
    [Fintype ↥(TCharC D)] [Fintype (VCocycle DD ρ)]
    (S : CountSections DD σ) (hσ : ∀ cc : DD.C0, piQbar DD (σ cc) = cc) (Dsc : Descent D)
    (htriv : ∀ (γ : Γ) (m : ZMod 2), γ • m = m)
    (hH2 : Nat.card (H2 Γ (ZMod 2)) = 2)
    (hsep : ∀ c : VCocycle DD ρ, (∀ χ : ↥(TCharC D), betaChi S hσ χ c = 0) → TLiftable hσ c) :
    (∑ c : VCocycle DD ρ, ∑ χ : ↥(TCharC D),
        sign (betaChi S hσ χ c) * (1 + sign (betaXi hσ Dsc c)))
      = 2 * (Nat.card ↥(TCharC D) : ℤ)
        * (Nat.card {c : VCocycle DD ρ // TLiftable hσ c ∧ betaXi hσ Dsc c = 0} : ℤ) := by
  classical
  have hc : ∀ c : VCocycle DD ρ, (∑ χ : ↥(TCharC D),
      sign (betaChi S hσ χ c) * (1 + sign (betaXi hσ Dsc c)))
      = if TLiftable hσ c ∧ betaXi hσ Dsc c = 0
        then 2 * (Nat.card ↥(TCharC D) : ℤ) else 0 := by
    intro c
    rw [← Finset.sum_mul, sum_sign_betaChi_eq_iteN S hσ htriv hH2 hsep c, one_add_sign]
    by_cases h1 : TLiftable hσ c <;> by_cases h2 : betaXi hσ Dsc c = 0
    · rw [if_pos h1, if_pos h2, if_pos ⟨h1, h2⟩]; ring
    · rw [if_pos h1, if_neg h2, if_neg (fun h => h2 h.2)]; ring
    · rw [if_neg h1, if_pos h2, if_neg (fun h => h1 h.1)]; ring
    · rw [if_neg h1, if_neg h2, if_neg (fun h => h1 h.1)]; ring
  rw [Finset.sum_congr rfl fun c _ => hc c, ← Finset.sum_filter,
    Finset.sum_const, Nat.card_eq_fintype_card (α := {c : VCocycle DD ρ //
      TLiftable hσ c ∧ betaXi hσ Dsc c = 0}), Fintype.card_subtype]
  ring

open scoped Classical in
omit [IsTopologicalGroup Γ] in
/-- **Way 2, first double sum**.  Verbatim copy of `sum_sum_sign_betaChi_eq_card`
(`GQ2/VLiftCount.lean:676`). -/
private theorem sum_sum_sign_betaChi_eq_cardN
    [Fintype ↥(TCharC D)] [Fintype (VCocycle DD ρ)]
    (S : CountSections DD σ) (hσ : ∀ cc : DD.C0, piQbar DD (σ cc) = cc)
    (haff : ∀ (χ : ↥(TCharC D)) (c c' : VCocycle DD ρ),
      betaChi S hσ χ (c + c')
        = betaChi S hσ χ c + betaChi S hσ χ c' + betaChi S hσ χ (0 : VCocycle DD ρ))
    (hpartial : ∀ χ : ↥(TCharC D), χ ≠ 0 →
      ∃ c : VCocycle DD ρ, betaChi S hσ χ c ≠ betaChi S hσ χ (0 : VCocycle DD ρ)) :
    (∑ χ : ↥(TCharC D), ∑ c : VCocycle DD ρ, sign (betaChi S hσ χ c))
      = (Nat.card (VCocycle DD ρ) : ℤ) := by
  classical
  rw [Finset.sum_eq_single (0 : ↥(TCharC D))]
  · rw [Finset.sum_congr rfl fun c _ => by rw [betaChi_zero_char S hσ c, sign_zero],
      Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one,
      Nat.card_eq_fintype_card]
  · intro χ _ hχ
    have hadd : ∀ a b : VCocycle DD ρ,
        (betaChi S hσ χ (a + b) + betaChi S hσ χ (0 : VCocycle DD ρ))
          = (betaChi S hσ χ a + betaChi S hσ χ (0 : VCocycle DD ρ))
            + (betaChi S hσ χ b + betaChi S hσ χ (0 : VCocycle DD ρ)) := by
      intro a b
      rw [haff χ a b]
      ring
    have hnz : ¬∀ a : VCocycle DD ρ,
        betaChi S hσ χ a + betaChi S hσ χ (0 : VCocycle DD ρ) = 0 := by
      intro hall
      obtain ⟨c₀, hc₀⟩ := hpartial χ hχ
      have := hall c₀
      have hchar : ∀ x y : ZMod 2, x + y = 0 → x = y := by decide
      exact hc₀ (hchar _ _ this)
    have hzero := sum_sign_eq_zero
      (fun a : VCocycle DD ρ => betaChi S hσ χ a + betaChi S hσ χ (0 : VCocycle DD ρ)) hadd hnz
    rw [finsum_eq_sum_of_fintype] at hzero
    calc ∑ c : VCocycle DD ρ, sign (betaChi S hσ χ c)
        = ∑ c : VCocycle DD ρ, sign (betaChi S hσ χ (0 : VCocycle DD ρ))
            * sign (betaChi S hσ χ c + betaChi S hσ χ (0 : VCocycle DD ρ)) := by
          refine Finset.sum_congr rfl fun c _ => ?_
          rw [← sign_add]
          congr 1
          have hchar : ∀ x y : ZMod 2, x = y + (x + y) := by decide
          exact hchar _ _
      _ = sign (betaChi S hσ χ (0 : VCocycle DD ρ)) * ∑ c : VCocycle DD ρ,
            sign (betaChi S hσ χ c + betaChi S hσ χ (0 : VCocycle DD ρ)) := by rw [Finset.mul_sum]
      _ = 0 := by rw [hzero, mul_zero]
  · intro h
    exact absurd (Finset.mem_univ _) h

open scoped Classical in
omit [IsTopologicalGroup Γ] in
/-- **Way 2, second double sum**.  Verbatim copy of `sum_sum_sign_betaChi_add_betaXi_eq`
(`GQ2/VLiftCount.lean:726`). -/
private theorem sum_sum_sign_betaChi_add_betaXi_eqN
    [Fintype ↥(TCharC D)] [Fintype (VCocycle DD ρ)]
    (S : CountSections DD σ) (hσ : ∀ cc : DD.C0, piQbar DD (σ cc) = cc) (Dsc : Descent D)
    (Δ : ↥(TCharC D) → DD.C0 × DD.C0 → ZMod 2) (sh : ↥(TCharC D) → VCocycle DD ρ)
    (hkey : ∀ (χ : ↥(TCharC D)) (c : VCocycle DD ρ),
      betaChi S hσ χ c + betaXi hσ Dsc c
        = QZero DD ρ (c + sh χ) + iotaB (pullCoc (fun γ => rho0 DD ρ γ) (Δ χ))) :
    (∑ χ : ↥(TCharC D), ∑ c : VCocycle DD ρ,
        sign (betaChi S hσ χ c + betaXi hσ Dsc c))
      = (∑ᶠ c : VCocycle DD ρ, sign (QZero DD ρ c))
        * ∑ χ : ↥(TCharC D), sign (iotaB (pullCoc (fun γ => rho0 DD ρ γ) (Δ χ))) := by
  classical
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun χ _ => ?_
  calc ∑ c : VCocycle DD ρ, sign (betaChi S hσ χ c + betaXi hσ Dsc c)
      = ∑ c : VCocycle DD ρ, sign (QZero DD ρ (c + sh χ))
          * sign (iotaB (pullCoc (fun γ => rho0 DD ρ γ) (Δ χ))) := by
        refine Finset.sum_congr rfl fun c _ => ?_
        rw [← sign_add, hkey χ c]
    _ = (∑ c : VCocycle DD ρ, sign (QZero DD ρ (c + sh χ)))
          * sign (iotaB (pullCoc (fun γ => rho0 DD ρ γ) (Δ χ))) := by
        rw [← Finset.sum_mul]
    _ = (∑ᶠ c : VCocycle DD ρ, sign (QZero DD ρ c))
          * sign (iotaB (pullCoc (fun γ => rho0 DD ρ γ) (Δ χ))) := by
        congr 1
        rw [finsum_eq_sum_of_fintype]
        exact Fintype.sum_equiv (Equiv.addRight (sh χ))
          (fun c => sign (QZero DD ρ (c + sh χ))) (fun c => sign (QZero DD ρ c))
          (fun c => rfl)

/-! ## The `hZcard`-free master identity -/

open scoped Classical in
/-- **The master count, before normalization** — the reusable artifact this file exists to
create.  It is `GQ2.SectionEight.AffineTLift.two_mul_card_centralImage`
(`GQ2/VLiftCount.lean:764`) with the terminal `rw [hZcard, hGaussZ]` *not yet performed*: the
right-hand side still carries the raw `#Z¹(V)` and the raw base-Gauss sum.

Both the model's normalization (`#Z¹ = #V·#V`, `G(Q⁰) = #V·G0`) and the degree-`n`
normalization (`#Z¹ = #V·vH`) are immediate from here, so the parameterization costs no
mathematics — only the `private`-chain copy documented in the header. -/
private theorem masterCountRaw
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ] [ContinuousSMul Γ (ZMod 2)]
    (S : CountSections DD σ) (hσ : ∀ cc : DD.C0, piQbar DD (σ cc) = cc) (Dsc : Descent D)
    (htriv : ∀ (γ : Γ) (m : ZMod 2), γ • m = m)
    (hfg : ∃ s : Finset Γ, (Subgroup.closure (s : Set Γ)).topologicalClosure = ⊤)
    (hH2 : Nat.card (H2 Γ (ZMod 2)) = 2)
    (hsep : ∀ c : VCocycle DD ρ, (∀ χ : ↥(TCharC D), betaChi S hσ χ c = 0) → TLiftable hσ c)
    (haff : ∀ (χ : ↥(TCharC D)) (c c' : VCocycle DD ρ),
      betaChi S hσ χ (c + c')
        = betaChi S hσ χ c + betaChi S hσ χ c' + betaChi S hσ χ (0 : VCocycle DD ρ))
    (hpartial : ∀ χ : ↥(TCharC D), χ ≠ 0 →
      ∃ c : VCocycle DD ρ, betaChi S hσ χ c ≠ betaChi S hσ χ (0 : VCocycle DD ρ))
    (Δ : ↥(TCharC D) → DD.C0 × DD.C0 → ZMod 2) (sh : ↥(TCharC D) → VCocycle DD ρ)
    (hkey : ∀ (χ : ↥(TCharC D)) (c : VCocycle DD ρ),
      betaChi S hσ χ c + betaXi hσ Dsc c
        = QZero DD ρ (c + sh χ) + iotaB (pullCoc (fun γ => rho0 DD ρ γ) (Δ χ))) :
    2 * (Nat.card ↥(TCharC D) : ℤ)
        * (Nat.card ↥(Set.range (fun f : {f : MLifts D ρ // f.Central} => redT ρ f.1)) : ℤ)
      = (Nat.card (VCocycle DD ρ) : ℤ)
        + (∑ᶠ c : VCocycle DD ρ, sign (QZero DD ρ c))
          * ∑ᶠ χ : ↥(TCharC D), sign (iotaB (pullCoc (fun γ => rho0 DD ρ γ) (Δ χ))) := by
  classical
  haveI : Finite (VCocycle DD ρ) := finite_vcocycle σ hσ hfg
  haveI : Fintype (VCocycle DD ρ) := Fintype.ofFinite _
  haveI : Fintype ↥(TCharC D) := Fintype.ofFinite _
  -- Step 0: transport the count to the cocycle layer and the (131)-characterization
  have hbridge : Nat.card ↥(Set.range (fun f : {f : MLifts D ρ // f.Central} => redT ρ f.1))
      = Nat.card {c : VCocycle DD ρ // TLiftable hσ c ∧ betaXi hσ Dsc c = 0} := by
    rw [card_range_redT_eq hσ]
    exact Nat.card_congr (Equiv.subtypeEquivRight fun c =>
      mem_centralImage_iff hσ Dsc htriv c)
  -- Step 1: split the master double sum
  have hway1 := doubleSum_eq_two_mul_card_liftableN S hσ Dsc htriv hH2 hsep
  have hsplit : (∑ c : VCocycle DD ρ, ∑ χ : ↥(TCharC D),
        sign (betaChi S hσ χ c) * (1 + sign (betaXi hσ Dsc c)))
      = (∑ χ : ↥(TCharC D), ∑ c : VCocycle DD ρ, sign (betaChi S hσ χ c))
        + ∑ χ : ↥(TCharC D), ∑ c : VCocycle DD ρ,
            sign (betaChi S hσ χ c + betaXi hσ Dsc c) := by
    rw [Finset.sum_comm, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun χ _ => ?_
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [sign_add]
    ring
  -- Step 2: assemble — Way 1 (central count) against Way 2 (base Gauss transport)
  rw [hbridge, ← hway1, hsplit,
    sum_sum_sign_betaChi_eq_cardN S hσ haff hpartial,
    sum_sum_sign_betaChi_add_betaXi_eqN S hσ Dsc Δ sh hkey,
    finsum_eq_sum_of_fintype (f := fun χ : ↥(TCharC D) =>
      sign (iotaB (pullCoc (fun γ => rho0 DD ρ γ) (Δ χ))))]

/-! ## The parameterized master count -/

open scoped Classical in
/-- **The master count at a parameterized `#H¹` multiplicity** (memo §4.1(c)).  Clone of
`GQ2.SectionEight.AffineTLift.two_mul_card_centralImage` (`GQ2/VLiftCount.lean:764`) with the
**inner** `|V|` of `hZcard` replaced by an opaque `vH` — the record field `SN.h1Mult |V|` at
instantiation.  The outer `|V|` (the `#B¹` normalization of `hGaussZ`) is degree-independent
and does not move (memo §1.3).

Sole consumer: `hMobst_of_residuesK` (this part's `Phase140Assembly.lean`), matching the
model's sole consumer `GQ2/Phase140/Assembly.lean:191`. -/
theorem two_mul_card_centralImageN
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ] [ContinuousSMul Γ (ZMod 2)]
    (S : CountSections DD σ) (hσ : ∀ cc : DD.C0, piQbar DD (σ cc) = cc) (Dsc : Descent D)
    (htriv : ∀ (γ : Γ) (m : ZMod 2), γ • m = m)
    (hfg : ∃ s : Finset Γ, (Subgroup.closure (s : Set Γ)).topologicalClosure = ⊤)
    (hH2 : Nat.card (H2 Γ (ZMod 2)) = 2)
    (hsep : ∀ c : VCocycle DD ρ, (∀ χ : ↥(TCharC D), betaChi S hσ χ c = 0) → TLiftable hσ c)
    (haff : ∀ (χ : ↥(TCharC D)) (c c' : VCocycle DD ρ),
      betaChi S hσ χ (c + c')
        = betaChi S hσ χ c + betaChi S hσ χ c' + betaChi S hσ χ (0 : VCocycle DD ρ))
    (hpartial : ∀ χ : ↥(TCharC D), χ ≠ 0 →
      ∃ c : VCocycle DD ρ, betaChi S hσ χ c ≠ betaChi S hσ χ (0 : VCocycle DD ρ))
    (Δ : ↥(TCharC D) → DD.C0 × DD.C0 → ZMod 2) (sh : ↥(TCharC D) → VCocycle DD ρ)
    (hkey : ∀ (χ : ↥(TCharC D)) (c : VCocycle DD ρ),
      betaChi S hσ χ c + betaXi hσ Dsc c
        = QZero DD ρ (c + sh χ) + iotaB (pullCoc (fun γ => rho0 DD ρ γ) (Δ χ)))
    (vH : ℕ) (G0 : ℤ)
    (hZcard : Nat.card (VCocycle DD ρ) = Nat.card DD.Vmod * vH)
    (hGaussZ : ∑ᶠ c : VCocycle DD ρ, sign (QZero DD ρ c) = (Nat.card DD.Vmod : ℤ) * G0) :
    2 * (Nat.card ↥(TCharC D) : ℤ)
        * (Nat.card ↥(Set.range (fun f : {f : MLifts D ρ // f.Central} => redT ρ f.1)) : ℤ)
      = (Nat.card DD.Vmod : ℤ) * ((vH : ℤ)
          + G0 * ∑ᶠ χ : ↥(TCharC D),
              sign (iotaB (pullCoc (fun γ => rho0 DD ρ γ) (Δ χ)))) := by
  rw [masterCountRaw S hσ Dsc htriv hfg hH2 hsep haff hpartial Δ sh hkey, hZcard, hGaussZ,
    Nat.cast_mul]
  ring

/-! ## The `vH = |V|` regression

At the model's normalization the parameterized statement **is** the model's — the clone did not
weaken anything.  (This is the `n = 1` bridge SD2 threads through `SN.h1Mult |V| = |V|`, which is
`standardNumerics_one_h1Mult`, a `pow_one` and not `rfl`; see `Numerics.lean:105`.) -/
theorem two_mul_card_centralImageN_eq
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ] [ContinuousSMul Γ (ZMod 2)]
    (S : CountSections DD σ) (hσ : ∀ cc : DD.C0, piQbar DD (σ cc) = cc) (Dsc : Descent D)
    (htriv : ∀ (γ : Γ) (m : ZMod 2), γ • m = m)
    (hfg : ∃ s : Finset Γ, (Subgroup.closure (s : Set Γ)).topologicalClosure = ⊤)
    (hH2 : Nat.card (H2 Γ (ZMod 2)) = 2)
    (hsep : ∀ c : VCocycle DD ρ, (∀ χ : ↥(TCharC D), betaChi S hσ χ c = 0) → TLiftable hσ c)
    (haff : ∀ (χ : ↥(TCharC D)) (c c' : VCocycle DD ρ),
      betaChi S hσ χ (c + c')
        = betaChi S hσ χ c + betaChi S hσ χ c' + betaChi S hσ χ (0 : VCocycle DD ρ))
    (hpartial : ∀ χ : ↥(TCharC D), χ ≠ 0 →
      ∃ c : VCocycle DD ρ, betaChi S hσ χ c ≠ betaChi S hσ χ (0 : VCocycle DD ρ))
    (Δ : ↥(TCharC D) → DD.C0 × DD.C0 → ZMod 2) (sh : ↥(TCharC D) → VCocycle DD ρ)
    (hkey : ∀ (χ : ↥(TCharC D)) (c : VCocycle DD ρ),
      betaChi S hσ χ c + betaXi hσ Dsc c
        = QZero DD ρ (c + sh χ) + iotaB (pullCoc (fun γ => rho0 DD ρ γ) (Δ χ)))
    (G0 : ℤ)
    (hZcard : Nat.card (VCocycle DD ρ) = Nat.card DD.Vmod * Nat.card DD.Vmod)
    (hGaussZ : ∑ᶠ c : VCocycle DD ρ, sign (QZero DD ρ c) = (Nat.card DD.Vmod : ℤ) * G0) :
    2 * (Nat.card ↥(TCharC D) : ℤ)
        * (Nat.card ↥(Set.range (fun f : {f : MLifts D ρ // f.Central} => redT ρ f.1)) : ℤ)
      = (Nat.card DD.Vmod : ℤ) * ((Nat.card DD.Vmod : ℤ)
          + G0 * ∑ᶠ χ : ↥(TCharC D),
              sign (iotaB (pullCoc (fun γ => rho0 DD ρ γ) (Δ χ)))) :=
  two_mul_card_centralImageN S hσ Dsc htriv hfg hH2 hsep haff hpartial Δ sh hkey
    (Nat.card DD.Vmod) G0 hZcard hGaussZ

end GQ2.Dyadic
