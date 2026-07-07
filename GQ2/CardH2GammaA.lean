import GQ2.RStageGammaA

/-!
# P-16d6e6: `#H²(Γ_A, 𝔽₂) = 2`, unconditionally  (the `hcard_A` residue of P-16d6e5)

The existing `LedgerGammaA.card_H2_gammaA_eq_two` (P-16c4) proves `#H²(Γ_A, 𝔽₂) = 2` but takes a
**`NoDescent`** radical-cover datum as input (the nonzero variation class is built from a nonzero
radical edge).  The R-stage assembly of P-16d6e5 needs the bare cardinality with **no cover data
in scope** (the "zero-edge" regime), so this file discharges the `NoDescent` hypothesis once and
for all against a **concrete witness**:

  the central extension `𝔽₂ → D₈ → 𝔽₂²` with `T = M = ⟨s̄⟩` and `q ≡ 0`.

`T` lies in the (whole) radical of the zero form, and the cover has **no descent**: the two lifts
`sr 0`, `sr 2 = (sr 0)·z` of the generator of `T` are swapped by conjugation by `r 1`, so neither
`𝔽₂`-line complementing `⟨z⟩` in `p⁻¹(T)` is normal.  Feeding this into `card_H2_gammaA_eq_two`
(via any surjection `Γ_A ↠ 𝔽₂²/⟨s̄⟩`, built here by descending an order-2 marking) yields the
unconditional

  `card_H2_gammaA_unit : Nat.card (H2 GA (ZMod 2)) = 2`.

Wired into the R-stage: `stageR136_gammaA` (the hypothesis-free (136) identity for the candidate
source) drops the `hcard_A` argument of `RStageGammaA.stageR136_gammaA_of_hcard`.

All finite-group facts are `decide`d; every declaration is std-3 (no B-axioms — the candidate
duality route is axiom-free, and the witness is elementary group theory).
-/

namespace GQ2

namespace CardH2GammaA

open DihedralGroup SectionEight CentralObstruction ContCoh WordCohBridge

/-! ## The concrete witness `𝔽₂ → D₈ → 𝔽₂²` -/

/-- The base group `𝔽₂² = ` Klein four `= DihedralGroup 2`. -/
abbrev Base : Type := DihedralGroup 2
/-- The cover `D₈ = DihedralGroup 4`. -/
abbrev Cov : Type := DihedralGroup 4

local instance : TopologicalSpace Base := ⊥
local instance : DiscreteTopology Base := ⟨rfl⟩
local instance : TopologicalSpace Cov := ⊥
local instance : DiscreteTopology Cov := ⟨rfl⟩

/-- The "index parity" character `𝔽₂² → 𝔽₂`, whose kernel is `T = M = ⟨s̄⟩`. -/
def φ₀ : Base →* Multiplicative (ZMod 2) where
  toFun g := match g with
    | .r i => Multiplicative.ofAdd i
    | .sr i => Multiplicative.ofAdd i
  map_one' := by decide
  map_mul' := by decide

/-- `M = T = ⟨s̄⟩ = ker φ₀ = {1, sr 0}` — the radical layer. -/
def Mlayer : Subgroup Base := φ₀.ker

instance : DecidablePred (· ∈ Mlayer) := fun _ => decidable_of_iff _ MonoidHom.mem_ker.symm
instance : Mlayer.Normal := φ₀.normal_ker

/-- The cover projection `D₈ → 𝔽₂²`, reducing the rotation index `ZMod 4 → ZMod 2`. -/
def cover_p : Cov →* Base where
  toFun g := match g with
    | .r i => .r (i.val : ZMod 2)
    | .sr i => .sr (i.val : ZMod 2)
  map_one' := by decide
  map_mul' := by decide

/-- The central double cover `D₈ ↠ 𝔽₂²` with kernel `⟨z⟩`, `z = r 2`. -/
noncomputable def cover : CentralCover Base where
  cover := Cov
  p := cover_p
  surj := by decide
  z := r 2
  z_ne := by decide
  z_sq := by decide
  central := by decide
  ker_eq := by
    apply le_antisymm
    · intro x hx
      have hx2 : x = r 0 ∨ x = r 2 := by
        revert hx; rw [MonoidHom.mem_ker]; revert x; decide
      rcases hx2 with rfl | rfl
      · exact one_mem _
      · exact Subgroup.mem_zpowers _
    · rw [Subgroup.zpowers_le, MonoidHom.mem_ker]; decide

/-- Squares of cover elements over `M` land in `⟨z⟩` — here trivially `= 1`, since `q ≡ 0`
(`sr i` are involutions and `r 0, r 2` square to `1`). -/
theorem cover_sq (x : Cov) (hx : cover_p x ∈ Mlayer) : x * x = 1 := by
  revert hx; revert x; decide

/-- **The radical-cover datum of the witness**: `M = T = ⟨s̄⟩`, `q ≡ 0`. -/
noncomputable def datum : RadicalCoverData Base where
  C := cover
  M := Mlayer
  hM := inferInstance
  T := Mlayer
  hT := inferInstance
  hTM := le_refl _
  helem := by decide
  hcomm := by decide
  q := fun _ => 0
  hq := fun x hx => by
    show x * x = (r 2) ^ (((0 : ZMod 2)).val)
    rw [ZMod.val_zero, pow_zero]
    exact cover_sq x hx
  hrad := by intro t _ m _; simp [polarMul]
  hTzero := fun _ _ => rfl

/-- **The witness has no descent**: `p⁻¹(T) = {r0, r2, sr0, sr2}` is elementary abelian, but the
two `𝔽₂`-lines `⟨sr 0⟩`, `⟨sr 2⟩` complementing `⟨z⟩ = ⟨r 2⟩` are swapped by conjugation by
`r 1` (`r 1 · sr 0 · r 1⁻¹ = sr 2`), so neither is normal — and `sr 0 · sr 2 = r 2 = z`. -/
theorem datum_noDescent : datum.NoDescent := by
  rintro ⟨N, hNorm, hmap, hz⟩
  -- `sr 0 ∈ M = p(N)`, so some `n ∈ N` has `p n = sr 0`
  have hsr0M : (sr 0 : Base) ∈ Subgroup.map datum.C.p N := by
    rw [hmap]; show (sr 0 : Base) ∈ Mlayer; decide
  obtain ⟨n, hnN, hpn⟩ := Subgroup.mem_map.mp hsr0M
  have hncase : n = sr 0 ∨ n = sr 2 :=
    (by decide : ∀ m : Cov, cover_p m = sr 0 → m = sr 0 ∨ m = sr 2) n hpn
  -- conjugation by `r 1` swaps `sr 0 ↔ sr 2`, so both lie in `N`
  have hboth : (sr 0 : Cov) ∈ N ∧ (sr 2 : Cov) ∈ N := by
    rcases hncase with rfl | rfl
    · refine ⟨hnN, ?_⟩
      have h : (r 1 * sr 0 * (r 1)⁻¹ : Cov) ∈ N := hNorm.conj_mem _ hnN (r 1)
      rwa [show (r 1 * sr 0 * (r 1)⁻¹ : Cov) = sr 2 from by decide] at h
    · refine ⟨?_, hnN⟩
      have h : (r 1 * sr 2 * (r 1)⁻¹ : Cov) ∈ N := hNorm.conj_mem _ hnN (r 1)
      rwa [show (r 1 * sr 2 * (r 1)⁻¹ : Cov) = sr 0 from by decide] at h
  -- but then `z = r 2 = sr 0 · sr 2 ∈ N`, contradiction
  have hzN : (r 2 : Cov) ∈ N := by
    have h : (sr 0 * sr 2 : Cov) ∈ N := N.mul_mem hboth.1 hboth.2
    rwa [show (sr 0 * sr 2 : Cov) = r 2 from by decide] at h
  exact hz hzN

/-! ## A surjection `Γ_A ↠ 𝔽₂²/⟨s̄⟩` and the unconditional cardinality -/

instance : DecidableEq (Base ⧸ Mlayer) :=
  Quotient.decidableEq (d := fun _ _ => decidable_of_iff _ QuotientGroup.leftRel_apply.symm)

local instance : DiscreteTopology (Base ⧸ Mlayer) :=
  (discreteTopology_quotient datum : DiscreteTopology (Base ⧸ datum.M))

/-- The order-2 marking of `𝔽₂²/⟨s̄⟩` sending `σ ↦ [r̄]` (the nonzero class) and the rest to `1` —
trivial wild generators, so admissibility is elementary. -/
def qmark : Marking (Base ⧸ Mlayer) := ⟨QuotientGroup.mk (r 1), 1, 1, 1⟩

/-- Every class in `𝔽₂²/⟨s̄⟩` is `1` or `[r̄]` (the quotient has order 2). -/
theorem quotient_cases (b : Base) :
    (QuotientGroup.mk b : Base ⧸ Mlayer) = 1 ∨ (QuotientGroup.mk b : Base ⧸ Mlayer)
      = QuotientGroup.mk (r 1) := by
  revert b; decide

theorem qmark_admissible : qmark.Admissible := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- Generates: `[r̄]` alone generates the order-2 quotient
    show Subgroup.closure {qmark.σ, qmark.τ, qmark.x₀, qmark.x₁} = ⊤
    rw [eq_top_iff]; intro x _
    obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective x
    have hσ : qmark.σ ∈ Subgroup.closure {qmark.σ, qmark.τ, qmark.x₀, qmark.x₁} :=
      Subgroup.subset_closure (by left; rfl)
    rcases quotient_cases b with h | h
    · rw [h]; exact one_mem _
    · rw [h]; exact hσ
  · -- TameRel: `τ = 1`
    show conjP qmark.τ qmark.σ = qmark.τ ^ 2
    show conjP (1 : Base ⧸ Mlayer) (QuotientGroup.mk (r 1)) = (1 : Base ⧸ Mlayer) ^ 2
    rw [conjP, mul_one, inv_mul_cancel, one_pow]
  · -- WildRel: trivial wild generators
    exact qmark.wildRel_of_trivial_wild rfl rfl
      (powOmega2_eq_one_of_odd (by
        show Odd (orderOf (1 : Base ⧸ Mlayer)); rw [orderOf_one]; decide))
  · -- Pro2Core: `⟨x₀,x₁⟩ = ⟨1,1⟩` normally closes to `⊥`
    show IsPGroup 2 (Subgroup.normalClosure {qmark.x₀, qmark.x₁})
    have hbot : Subgroup.normalClosure ({qmark.x₀, qmark.x₁} : Set (Base ⧸ Mlayer)) = ⊥ := by
      rw [eq_bot_iff]
      refine Subgroup.normalClosure_le_normal ?_
      rintro x (rfl | rfl) <;> exact Subgroup.mem_bot.mpr rfl
    rw [hbot]; exact IsPGroup.of_bot

/-- The chosen surjection `ρ : Γ_A ↠ 𝔽₂²/⟨s̄⟩`, by descending `qmark`. -/
noncomputable def rho : ContinuousMonoidHom GA (Base ⧸ Mlayer) :=
  Marking.descend qmark qmark_admissible

theorem rho_surjective : Function.Surjective rho :=
  Marking.descend_surjective qmark qmark_admissible

/-- **`#H²(Γ_A, 𝔽₂) = 2`, unconditionally** (P-16d6e6, over the raw quotient `GA`).  The `NoDescent`
hypothesis of `LedgerGammaA.card_H2_gammaA_eq_two` is discharged by the concrete witness
`datum`/`datum_noDescent`; `ρ = rho` is any surjection onto `𝔽₂²/⟨s̄⟩`. -/
theorem card_H2_gammaA_unit
    [DistribMulAction GA (ZMod 2)] [ContinuousSMul GA (ZMod 2)]
    (htriv : ∀ (x : GA) (m : ZMod 2), x • m = m) :
    Nat.card (H2 GA (ZMod 2)) = 2 :=
  LedgerGammaA.card_H2_gammaA_eq_two datum (tComplement_nonempty datum).some datum_noDescent
    rho rho_surjective htriv

/-! ## The `GammaA`-facing forms and the hypothesis-free (136) for the candidate source -/

section Assembly

open RStageGammaA SectionSeven

variable {H E : Type} [Group H] [TopologicalSpace H] [DiscreteTopology H] [Finite H]
  [CommGroup E] [TopologicalSpace E] [DiscreteTopology E] [Finite E]
variable {Y : Type} [Group Y] [TopologicalSpace Y] [DiscreteTopology Y] [Finite Y]
variable {T : MarkedTarget H E Y} {Blk : SectionSeven.MinimalBlock T.LY}

/-- **`#H²(Γ_A, 𝔽₂) = 2`** over the packaged `GammaA`, with its canonical trivial action
(`RStageGammaA.instDistribMulActionGammaA`).  This is the exact `hcard_A` residue that
`RStageGammaA.stageR136_gammaA_of_hcard` threads — supplied here unconditionally (P-16d6e6),
bridging the raw-quotient `GA` result across the `GA ≡ GammaA` defeq. -/
theorem card_H2_gammaA : Nat.card (H2 GammaA (ZMod 2)) = 2 := by
  letI : DistribMulAction GA (ZMod 2) := instDistribMulActionGammaA
  letI : ContinuousSMul GA (ZMod 2) := ⟨continuous_snd⟩
  exact card_H2_gammaA_unit (fun _ _ => rfl)

/-- **(136) for the block frame at the candidate source, hypothesis-free** (P-16d6e6): drops the
`hcard_A` argument of `RStageGammaA.stageR136_gammaA_of_hcard` by supplying `card_H2_gammaA`.
The remaining `hRK`/`hR2` are the `lemma_7_2` structural facts of the block; `hfg` is discharged
internally (`gammaA_topologicallyFinitelyGenerated`).  This is the `stageR136` field of the
candidate `RecursionInputs` bundle (the P-16d6e7 assembly), verbatim. -/
theorem stageR136_gammaA
    (hE2 : ∀ e : E, e ^ 2 = 1)
    (hRK : ∀ r ∈ Blk.R, ∀ k ∈ Blk.K, r * k = k * r)
    (hR2 : ∀ r ∈ Blk.R, r * r = 1)
    (b : ContinuousMonoidHom GammaA ↥boundarySubgroup) (F : BoundaryFrame H E) :
    (Nat.card (blockFrameImpl T Blk hE2).DR : ℤ) * exactImageCount b F T
      = (blockFrameImpl T Blk hE2).zR * ∑ᶠ l : (blockFrameImpl T Blk hE2).DR,
          (2 * ((blockFrameImpl T Blk hE2).mB b F l : ℤ)
            - exactImageCount b F (blockFrameImpl T Blk hE2).TB) :=
  stageR136_gammaA_of_hcard hE2 hRK hR2 card_H2_gammaA b F

end Assembly

end CardH2GammaA

end GQ2
