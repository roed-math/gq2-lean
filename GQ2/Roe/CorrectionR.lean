/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Opus-4.8 and Fable-5
-/
import GQ2.RStage.GammaA
import GQ2.WordCohBridgeR

/-!
# The `Γ_R` relator-correction calculus

The Roe-candidate twin of the correction layer of `GQ2/RStage/GammaA.lean` (sections
`WildCorrection`, `PushDescent`, `WordLiftMul`) — the per-cover algebra the `Γ_R` `(136)`-stage
separation argument (ticket R31e) and the `Γ_R` base-change/obstruction layers (R31f/R31g) run on.

Two independent pieces:

* **Relator death along any continuous hom from `Γ_R`** (no surjectivity, unlike
  `markC_admissible_R`): `push_tameRelR` / `push_wildRelR`, from `tameRelator_mem_NR` /
  `wildRelatorR_mem_NR`.
* **The correction ledger of the Roe word.**  Correcting a marking's four generators by *central
  involutions* `r⃗` (the shape of the kernel `R/l ≅ 𝔽₂` at an L4 cover) shifts the Roe wild relator
  value by exactly the τ-correction:

    `wildValueR_correction : (corrMark t r₀ r₁ r₂ r₃).wildValueR = r₁ * t.wildValueR`

  — the **same conclusion shape** as `Γ_A`'s `RStageGammaA.wildValue_correction`, so every
  downstream statement keeps its exact form.  The ledger, however, is computed by a different (and
  shorter) chain, because `Γ_A`'s nine auxiliary words `u₀,u₁,g₀,z₀,d₀,c₀,dg,h_c,h₀` do not occur
  in `r_R = (x₀^σ)⁻¹ · a · x₁² · c` (note eq. (1.2) ⟦eq:relators⟧).  The four Roe factors carry:

  | factor          | correction | why                                                       |
  |-----------------|------------|-----------------------------------------------------------|
  | `(x₀^σ)⁻¹`      | `r₂`       | `conjP_central_correction` (`r₀` cancels), then `r₂⁻¹ = r₂` |
  | `a = (x₀⁻³τ)^ω₂`| `r₂r₁`     | `corrMark_aR` (`r₂³ = r₂`) + `powOmega2_central_involution` |
  | `x₁²`           | none       | `corrMark_x1_sq` (`r₃² = 1`)                                |
  | `c = [x₁,y₁]`   | none       | `corrMark_cR` via `commP_central_correction`                |

  and `r₂ · r₂r₁ = r₁` is the whole ledger.

Finally the **general** (non-central) correction and base change at the Roe word:
`liftMarking_wildValueR_g`, `corrected_wildValueR` (stated at `d1FunR`), and `d1FunR_base_change`.

## Reused verbatim from `GQ2/RStage/GammaA.lean`, never cloned

`powOmega2_central_involution`, `tameValue_correction` (the tame relator is **shared** with `Γ_A`),
`conjP_central_correction`, `commP_central_correction`, `conjP_central_left`, the `corrMark`
definition itself together with `corrMark_sigma2` (`σ₂` is shared), `marking_ext`, and the
`WordLift` multiplication calculus `projW` / `mulW` / `baseW` / `liftMarking_map_projW` /
`liftMarking_tameValue_g` / `corrected_tameValue` / `d1Fun_base_change`.  Only the two `private`
helpers `central_mul_comm` / `central_mul_sq` are re-stated here (they are inaccessible across
modules); `central_pair` is not needed for the Roe word.

**Namespace.**  `GQ2.RStageGammaR`, mirroring `GQ2.RStageGammaA`, so that ticket R31e's port of
`hsep_hom_gammaA` reads name-for-name against the `Γ_A` original.
-/

namespace GQ2

open ContCoh WordCohBridgeR GQ2.FoxH RStageGammaA

namespace RStageGammaR

/-! ## Relator death along any continuous hom from `Γ_R` (L4) -/

section PushDescent

variable {G' : Type} [Group G'] [TopologicalSpace G'] [DiscreteTopology G'] [Finite G']

omit [DiscreteTopology G'] [Finite G'] in
/-- **Relators die along any continuous hom from `Γ_R`, tame** (`Γ_R` twin of
`RStageGammaA.push_tameRel`; NO surjectivity, unlike `markC_admissible_R`): the pushed marking of
any `f : Γ_R →ₜ* G'` satisfies the tame relation, because the tame relator word — **shared** with
`Γ_A` — lies in `N_R` (`tameRelator_mem_NR`). -/
theorem push_tameRelR (f : ContinuousMonoidHom GR G') : (Marking.pushR f).TameRel :=
  (Marking.map_tameRelator_eq_one_iff (f.comp (quotientMk NR)) univMarking).mp <| by
    show f (quotientMk NR univMarking.tameRelator) = 1
    rw [(quotientMk_eq_one_iff NR).mpr tameRelator_mem_NR, map_one]

/-- **Relators die along any continuous hom from `Γ_R`, wild** — the *Roe* wild relator word lies
in `N_R` (`wildRelatorR_mem_NR`, `GQ2/Roe/AdmissibleLimit.lean`).  `Γ_R` twin of
`RStageGammaA.push_wildRel`. -/
theorem push_wildRelR (f : ContinuousMonoidHom GR G') : (Marking.pushR f).WildRelR :=
  (Marking.map_wildRelatorR_eq_one_iff (f.comp (quotientMk NR)) univMarking).mp <| by
    show f (quotientMk NR univMarking.wildRelatorR) = 1
    rw [(quotientMk_eq_one_iff NR).mpr wildRelatorR_mem_NR, map_one]

end PushDescent

/-! ## L1-wild for the Roe word — the correction chain at central involutions -/

section WildCorrectionR

variable {Y' : Type*} [Group Y'] {t : Marking Y'} {r0 r1 r2 r3 : Y'}

/-- A product of central involutions is central.  (Local copy: `RStageGammaA.central_mul_comm` is
`private`, hence inaccessible across modules.) -/
private lemma centralR_mul_comm {a b : Y'} (ha : ∀ z : Y', Commute a z)
    (hb : ∀ z : Y', Commute b z) : ∀ z : Y', Commute (a * b) z := fun z => (ha z).mul_left (hb z)

/-- The square of a product of two central involutions is `1`.  (Local copy of the `private`
`RStageGammaA.central_mul_sq`.) -/
private lemma centralR_mul_sq {a b : Y'} (ha : ∀ z : Y', Commute a z) (ha2 : a ^ 2 = 1)
    (hb2 : b ^ 2 = 1) : (a * b) ^ 2 = 1 := by rw [(ha b).mul_pow, ha2, hb2, mul_one]

/-- A central involution is its own inverse. -/
private lemma centralR_inv {a : Y'} (ha2 : a ^ 2 = 1) : a⁻¹ = a :=
  inv_eq_of_mul_eq_one_right (by rw [← pow_two, ha2])

/-- **`a = (x₀⁻³τ)^ω₂` picks up `r₂r₁`.**  The `x₀`-correction survives the odd power `x₀⁻³`
(`r₂³ = r₂`) and combines centrally with the τ-correction, then `powOmega2_central_involution`
pushes the joint central involution `r₂r₁` out of the `ω₂`-power.  Replaces `Γ_A`'s dead
`corrMark_u0`/`corrMark_u1`. -/
theorem corrMark_aR [Finite Y'] (hr1 : ∀ z : Y', Commute r1 z) (hr2 : ∀ z : Y', Commute r2 z)
    (hr1sq : r1 ^ 2 = 1) (hr2sq : r2 ^ 2 = 1) :
    (corrMark t r0 r1 r2 r3).aR = (r2 * r1) * t.aR := by
  have hr2cube : r2 ^ 3 = r2 := by rw [pow_succ, hr2sq, one_mul]
  have hword : (((corrMark t r0 r1 r2 r3).x₀ ^ 3)⁻¹ * (corrMark t r0 r1 r2 r3).τ)
      = (r2 * r1) * ((t.x₀ ^ 3)⁻¹ * t.τ) := by
    show ((r2 * t.x₀) ^ 3)⁻¹ * (r1 * t.τ) = (r2 * r1) * ((t.x₀ ^ 3)⁻¹ * t.τ)
    rw [(hr2 t.x₀).mul_pow, hr2cube, mul_inv_rev, centralR_inv hr2sq,
      (hr2 ((t.x₀ ^ 3)⁻¹)).symm.eq, mul_assoc, ← mul_assoc ((t.x₀ ^ 3)⁻¹) r1 t.τ,
      (hr1 ((t.x₀ ^ 3)⁻¹)).symm.eq]
    group
  show powOmega2 (((corrMark t r0 r1 r2 r3).x₀ ^ 3)⁻¹ * (corrMark t r0 r1 r2 r3).τ)
    = (r2 * r1) * powOmega2 ((t.x₀ ^ 3)⁻¹ * t.τ)
  rw [hword]
  exact powOmega2_central_involution (r2 * r1) ((t.x₀ ^ 3)⁻¹ * t.τ)
    (centralR_mul_comm hr2 hr1) (centralR_mul_sq hr2 hr2sq hr1sq)

/-- **`y₁ = x₁^{σ₂}` picks up `r₃`** (the conjugating `σ₂`-correction `r₀` cancels) — the Roe
counterpart of `Γ_A`'s dead `corrMark_z0`, via the reused `conjP_central_correction` and the
reused `corrMark_sigma2` (`σ₂` is shared with `Γ_A`). -/
theorem corrMark_y1R [Finite Y'] (hr0 : ∀ z : Y', Commute r0 z) (hr3 : ∀ z : Y', Commute r3 z)
    (hr0sq : r0 ^ 2 = 1) : (corrMark t r0 r1 r2 r3).y1R = r3 * t.y1R := by
  show conjP (r3 * t.x₁) ((corrMark t r0 r1 r2 r3).sigma2) = r3 * conjP t.x₁ t.sigma2
  rw [corrMark_sigma2 hr0 hr0sq]
  exact conjP_central_correction t.x₁ t.sigma2 r3 r0 hr3 hr0

/-- **`c = [x₁, y₁]` is correction-free** — both entries carry the same correction `r₃`, and
`commP` kills central corrections (`commP_central_correction`).  Roe counterpart of `Γ_A`'s dead
`corrMark_c0`/`corrMark_hc`. -/
theorem corrMark_cR [Finite Y'] (hr0 : ∀ z : Y', Commute r0 z) (hr3 : ∀ z : Y', Commute r3 z)
    (hr0sq : r0 ^ 2 = 1) : (corrMark t r0 r1 r2 r3).cR = t.cR := by
  show commP (r3 * t.x₁) ((corrMark t r0 r1 r2 r3).y1R) = commP t.x₁ t.y1R
  rw [corrMark_y1R hr0 hr3 hr0sq]
  exact commP_central_correction t.x₁ t.y1R r3 r3 hr3 hr3

/-- **`x₁²` is correction-free** (`r₃² = 1`) — the third Roe factor. -/
theorem corrMark_x1_sq (hr3 : ∀ z : Y', Commute r3 z) (hr3sq : r3 ^ 2 = 1) :
    (corrMark t r0 r1 r2 r3).x₁ ^ 2 = t.x₁ ^ 2 := by
  show (r3 * t.x₁) ^ 2 = t.x₁ ^ 2
  rw [(hr3 t.x₁).mul_pow, hr3sq, one_mul]

/-- **L1 wild row for the Roe word, central 2-torsion**: the Roe wild relator value shifts by
exactly the τ-correction `r₁` —

  `wildValueR (r⃗ · ŷ) = r₁ · wildValueR ŷ`,

the **identical conclusion shape** to `Γ_A`'s `RStageGammaA.wildValue_correction`, reached by a
different ledger: `(x₀^σ)⁻¹` contributes `r₂` (its `r₀` cancels, and `r₂⁻¹ = r₂`), `a` contributes
`r₂r₁`, and `x₁²`, `c` are correction-free; the two `r₂`'s annihilate.  Matches
`d1FunR_wild`'s `x 1` slot. -/
theorem wildValueR_correction [Finite Y'] (hr0 : ∀ z : Y', Commute r0 z)
    (hr1 : ∀ z : Y', Commute r1 z) (hr2 : ∀ z : Y', Commute r2 z) (hr3 : ∀ z : Y', Commute r3 z)
    (hr0sq : r0 ^ 2 = 1) (hr1sq : r1 ^ 2 = 1) (hr2sq : r2 ^ 2 = 1) (hr3sq : r3 ^ 2 = 1) :
    (corrMark t r0 r1 r2 r3).wildValueR = r1 * t.wildValueR := by
  show (conjP (r2 * t.x₀) (r0 * t.σ))⁻¹ * (corrMark t r0 r1 r2 r3).aR
      * (corrMark t r0 r1 r2 r3).x₁ ^ 2 * (corrMark t r0 r1 r2 r3).cR
    = r1 * ((conjP t.x₀ t.σ)⁻¹ * t.aR * t.x₁ ^ 2 * t.cR)
  rw [conjP_central_correction t.x₀ t.σ r2 r0 hr2 hr0, corrMark_aR hr1 hr2 hr1sq hr2sq,
    corrMark_x1_sq hr3 hr3sq, corrMark_cR hr0 hr3 hr0sq, mul_inv_rev, centralR_inv hr2sq,
    show (conjP t.x₀ t.σ)⁻¹ * r2 * (r2 * r1 * t.aR) * t.x₁ ^ 2 * t.cR
      = (conjP t.x₀ t.σ)⁻¹ * (r2 * r2) * (r1 * (t.aR * t.x₁ ^ 2 * t.cR)) from by group,
    ← pow_two, hr2sq, mul_one, ← mul_assoc, (hr1 ((conjP t.x₀ t.σ)⁻¹)).symm.eq]
  group

/-- The **tame** row at a `corrMark` correction, from the reused `tameValue_correction` (the tame
relator is shared with `Γ_A`, and it does not read `x₀`/`x₁`, so the `r₂`/`r₃` corrections are
invisible to it). -/
theorem corrMark_tameValue (hr0 : ∀ z : Y', Commute r0 z) (hr1 : ∀ z : Y', Commute r1 z)
    (hr1sq : r1 ^ 2 = 1) : (corrMark t r0 r1 r2 r3).tameValue = r1 * t.tameValue :=
  tameValue_correction t.σ t.τ (r2 * t.x₀) (r3 * t.x₁) r0 r1 hr0 hr1 hr1sq

/-- **Stress test (consumption shape).**  Both `Γ_R` relator rows shift by the *same* central
involution `r₁` — the fact the `(136)`-stage separation argument (ticket R31e) consumes, and
exactly the `Γ_A` pairing `tameValue_correction`/`wildValue_correction`.  Pins that the Roe wild
ledger did not acquire a stray `r₀`/`r₂`/`r₃`. -/
theorem corrMark_relator_correction [Finite Y'] (hr0 : ∀ z : Y', Commute r0 z)
    (hr1 : ∀ z : Y', Commute r1 z) (hr2 : ∀ z : Y', Commute r2 z) (hr3 : ∀ z : Y', Commute r3 z)
    (hr0sq : r0 ^ 2 = 1) (hr1sq : r1 ^ 2 = 1) (hr2sq : r2 ^ 2 = 1) (hr3sq : r3 ^ 2 = 1) :
    (corrMark t r0 r1 r2 r3).tameValue = r1 * t.tameValue ∧
      (corrMark t r0 r1 r2 r3).wildValueR = r1 * t.wildValueR :=
  ⟨corrMark_tameValue hr0 hr1 hr1sq,
    wildValueR_correction hr0 hr1 hr2 hr3 hr0sq hr1sq hr2sq hr3sq⟩

/-- **Stress test (only the τ-correction survives).**  The corrected Roe wild relator value is
unchanged if `r₀`, `r₂`, `r₃` are replaced by `1` — an independent pin on the ledger's cancellation
(`r₂` against `r₂`, `r₃` against nothing since `x₁²` and `c` are correction-free). -/
theorem wildValueR_correction_tau_only [Finite Y'] (hr0 : ∀ z : Y', Commute r0 z)
    (hr1 : ∀ z : Y', Commute r1 z) (hr2 : ∀ z : Y', Commute r2 z) (hr3 : ∀ z : Y', Commute r3 z)
    (hr0sq : r0 ^ 2 = 1) (hr1sq : r1 ^ 2 = 1) (hr2sq : r2 ^ 2 = 1) (hr3sq : r3 ^ 2 = 1) :
    (corrMark t r0 r1 r2 r3).wildValueR = (corrMark t 1 r1 1 1).wildValueR := by
  rw [wildValueR_correction hr0 hr1 hr2 hr3 hr0sq hr1sq hr2sq hr3sq,
    wildValueR_correction (fun z => Commute.one_left z) hr1 (fun z => Commute.one_left z)
      (fun z => Commute.one_left z) (one_pow 2) hr1sq (one_pow 2) (one_pow 2)]

end WildCorrectionR

/-! ## The general (non-central) correction and base change at the Roe word

The `WordLift` multiplication calculus `projW`/`mulW`/`baseW` is relator-independent and reused
from `RStageGammaA`; only the three statements that mention `wildValueR`/`d1FunR` are re-derived. -/

section WordLiftMulR

variable {G : Type*} [Group G] {A : Type*} [AddCommGroup A] [DistribMulAction G A]

/-- The base coordinate of the evaluated **Roe** wild relator is the base Roe wild relator value
(finite: the `ω₂`-push).  `Γ_R` twin of `RStageGammaA.liftMarking_wildValue_g`. -/
theorem liftMarking_wildValueR_g [Finite G] [Finite A] (t : Marking G) (x : Fin 4 → A) :
    ((liftMarking t x).wildValueR).g = t.wildValueR := by
  have h := Marking.map_wildValueR (projW (A := A) (G := G)) (liftMarking t x)
  rw [liftMarking_map_projW] at h
  exact h.symm

/-- **The general relator correction, Roe wild row**: left-multiplying a marking's generators by
the `j`-realizations of coefficients `x` multiplies the Roe wild relator value by `j` of the wild
`d¹_R`-row.  (Evaluate `r_R` in `A ⋊ G` and push through `mulW`.)  `Γ_R` twin of
`RStageGammaA.corrected_wildValue`, stated at `d1FunR`. -/
theorem corrected_wildValueR [Finite G] [Finite A] (j : A → G)
    (hjmul : ∀ a b : A, j (a + b) = j a * j b)
    (hjconj : ∀ (g : G) (a : A), j (g • a) = g * j a * g⁻¹) (t : Marking G) (x : Fin 4 → A) :
    (Marking.mk (j (x 0) * t.σ) (j (x 1) * t.τ) (j (x 2) * t.x₀) (j (x 3) * t.x₁)).wildValueR
      = j ((d1FunR t x).2) * t.wildValueR := by
  have hmark : (liftMarking t x).map (mulW j hjmul hjconj)
      = Marking.mk (j (x 0) * t.σ) (j (x 1) * t.τ) (j (x 2) * t.x₀) (j (x 3) * t.x₁) := rfl
  rw [← hmark, Marking.map_wildValueR]
  show j ((liftMarking t x).wildValueR).u * ((liftMarking t x).wildValueR).g = _
  rw [liftMarking_wildValueR_g]
  rfl

/-- **`d¹_R` base change**: the Roe word differential only sees the action, so it is computed by
the pushed marking — `d1FunR (t.map f) x = d1FunR t x` when the `G`-action is pulled back along
`f`.  `Γ_R` twin of `RStageGammaA.d1Fun_base_change`; the tame slot is free because the tame row
is shared (`d1FunR_fst`), only the wild slot is re-derived. -/
theorem d1FunR_base_change [Finite G] [Finite A] {C : Type*} [Group C] [DistribMulAction C A]
    (f : G →* C) (hcompat : ∀ (g : G) (a : A), g • a = f g • a) (t : Marking G) (x : Fin 4 → A) :
    d1FunR (t.map f) x = d1FunR t x := by
  have hmark : (liftMarking t x).map (baseW f hcompat) = liftMarking (t.map f) x := rfl
  refine Prod.ext ?_ ?_
  · rw [d1FunR_fst, d1FunR_fst, d1Fun_base_change f hcompat t x]
  · show ((liftMarking (t.map f) x).wildValueR).u = ((liftMarking t x).wildValueR).u
    rw [← hmark, Marking.map_wildValueR]
    rfl

end WordLiftMulR

end RStageGammaR

end GQ2

/-! ### Paper-tag ledger (Roe note `paper/roe-presentation-verification.tex`; hand-maintained)

  * eq. (1.1) = ⟦eq:defwords⟧ — the auxiliary words `a`, `y₁`, `c` whose corrections are computed
    here (`corrMark_aR`, `corrMark_y1R`, `corrMark_cR`).
  * eq. (1.2) = ⟦eq:relators⟧ — the Roe relator whose correction ledger is `wildValueR_correction`.
-/
