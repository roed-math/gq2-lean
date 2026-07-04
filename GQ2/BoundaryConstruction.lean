import GQ2.Prop32
import GQ2.BoundaryFrame

/-!
# §3 boundary construction — Prop 3.10 (both halves) and Prop 3.14  (ticket P-25)

Proofs of the three §3-marked statements that fell through the P-09/P-10 closure
(`GQ2/SectionThreeMarked.lean`):

* **Prop 3.10, `Γ_A` half** (`prop_3_10_gammaA`): the maximal pro-`2` quotient of `Γ_A` is `Π`,
  matching the marked generators (`σ ↦ πσ`, `τ ↦ 1`, `x₀ ↦ πx₀`, `x₁ ↦ πx₁`).
* **Prop 3.10, local half** (`prop_3_10_local_marked`): `(Π, ν₂) ≅ (G_{ℚ₂}(2), ν_ur)`.
* **Prop 3.14** (`prop_3_14 : Nonempty BoundaryMaps`): the eq. (27) boundary data.

The analytical heart is the **word collapse**: at `τ = 1` (forced in every finite `2`-group
quotient by Lemma 3.1, `Tame.tame_odd_order`, since `τ` then has both odd and `2`-power order)
the auxiliary words trivialise (`u_i = x_i`, `d₀ = c₀ = d_g = h_c = 1`, `g₀ = σ²`,
`h₀ = σ⁻²x₀σ²·x₀`) and the wild relator (6) becomes the pro-2 relator (20) `= piRelator`.
Everything downstream mirrors `GQ2/Prop32.lean`'s `Γ_A`-side Prop 3.2 (`phiA`/`chiW`/`tameAEquiv`,
`isAdmissible_tameClassifier_level`, `NA_le_ker_tameClassifier`) one presentation up, using the
maximal-pro-`2`-quotient universal property (`GQ2/MaxProP.lean`: `proPKernel_le_ker`,
`maxProPHomEquiv`, `isProP_quotient_proPKernel`).
-/

namespace GQ2

open scoped Classical

/-! ## The wild-relator collapse at `τ = 1` -/

/-- **The word collapse.**  With `τ = 1` and `ω₂` acting as the identity on `σ, x₀, x₁`
(automatic in a `2`-group, where every element has `2`-power order), the wild relator word (6)
`h₀ · u₁⁻¹ · x₁^σ · c₀` equals the pro-`2` relator word (20)
`σ⁻²x₀σ² · x₀ · [x₁, σ]`. -/
theorem wildRelWord_eq {G : Type*} [Group G] (σ x₀ x₁ : G)
    (hσ : powOmega2 σ = σ) (hx0 : powOmega2 x₀ = x₀) (hx1 : powOmega2 x₁ = x₁) :
    (Marking.mk σ 1 x₀ x₁).h0 * (Marking.mk σ 1 x₀ x₁).u1⁻¹
        * conjP x₁ σ * (Marking.mk σ 1 x₀ x₁).c0
      = conjP x₀ (σ ^ 2) * x₀ * commP x₁ σ := by
  set t : Marking G := Marking.mk σ 1 x₀ x₁ with ht
  have hu0 : t.u0 = x₀ := by
    show powOmega2 (t.x₀ * t.τ) = x₀
    rw [show t.x₀ = x₀ from rfl, show t.τ = 1 from rfl, mul_one, hx0]
  have hu1 : t.u1 = x₁ := by
    show powOmega2 (t.x₁ * t.τ) = x₁
    rw [show t.x₁ = x₁ from rfl, show t.τ = 1 from rfl, mul_one, hx1]
  have hs2 : t.sigma2 = σ := by
    show powOmega2 t.σ = σ
    rw [show t.σ = σ from rfl, hσ]
  have hd0 : t.d0 = 1 := by
    rw [Marking.d0, hu0, show t.x₀ = x₀ from rfl, mul_inv_cancel]
  have hc0 : t.c0 = 1 := by
    rw [Marking.c0, hd0]; simp [commP]
  have hg0 : t.g0 = σ ^ 2 := by rw [Marking.g0, hs2]
  have hdg : t.dg = 1 := by rw [Marking.dg, hd0]; simp [conjP]
  have hhc : t.hc = 1 := by rw [Marking.hc, hdg, hd0]; simp [commP]
  have hh0 : t.h0 = conjP x₀ (σ ^ 2) * x₀ := by
    rw [Marking.h0, hdg, hd0, hhc, hg0, show t.x₀ = x₀ from rfl]
    simp
  rw [hh0, hu1, hc0, mul_one]
  simp only [conjP, commP]
  group

/-- The wild relation at `(σ, 1, x₀, x₁)` is equivalent to the pro-`2` relator vanishing, under
the `ω₂`-fixes hypotheses. -/
theorem wildRel_iff_piRelatorWord {G : Type*} [Group G] (σ x₀ x₁ : G)
    (hσ : powOmega2 σ = σ) (hx0 : powOmega2 x₀ = x₀) (hx1 : powOmega2 x₁ = x₁) :
    (Marking.mk σ 1 x₀ x₁).WildRel ↔ conjP x₀ (σ ^ 2) * x₀ * commP x₁ σ = 1 := by
  rw [Marking.WildRel, wildRelWord_eq σ x₀ x₁ hσ hx0 hx1]

/-! ## Both target groups are pro-`2` -/

/-- `Π` is a pro-`2` group (a maximal pro-`2` quotient). -/
theorem piBd_isProP : IsProP 2 PiBd :=
  isProP_quotient_proPKernel

/-- The maximal pro-`2` quotient of `Γ_A` is a pro-`2` group. -/
theorem maxProPGammaA_isProP : IsProP 2 (maxProPQuotient 2 GammaA) :=
  isProP_quotient_proPKernel

end GQ2
