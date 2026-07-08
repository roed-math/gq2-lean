import GQ2.RecursionSplice

/-!
# P-16d6c (c1b/c2 infrastructure): the `𝔽₂`-cover obstruction calculus and the
paper-faithful (140) reducer

Central `𝔽₂`-covers enter the (140) analysis through **one** scalar invariant: whether a
continuous hom `f : Γ → C₀` lifts through the cover.  This file builds that calculus and the
(140) reducer consuming it:

* **`iotaB`** — the coboundary indicator `ι_Γ` on 2-cochains (`0` iff the cochain is a continuous
  coboundary); additive on cocycles when `#H²(Γ,𝔽₂) = 2` (`iotaB_add` — the only place the
  source's `H²`-size enters, threaded as `hH2`).
* **`pullCoc`** — pullback of a finite-group 2-cochain along `f × f`, with `Z2`/`B2` membership
  lemmas (`pullCoc_mem_Z2`, `pullCoc_coboundary_mem_B2`).
* **`centralCover_lift_iff`** — for a central double cover equipped with a section of defect `δ`
  (`s c · s d = z^{δ(c,d)} · s(cd)` — `centralCoverOfCocycle_exists_section` supplies it for the
  phase covers): `f` lifts iff `f^*δ ∈ B²(Γ,𝔽₂)`.  This is the (141)-side liftability criterion
  and the `s_Γ(ζ)`-to-`n_{Γ,0}(ζ)` conversion.
* **`phaseSign`/`sum_phaseSign`** — the signed liftability count (141):
  `Σ_ρ (±1) = 2·n_{Γ,0}(ζ) − e_Γ(C)`.
* **`phase140_of_phaseObstruction`** — the **paper-faithful (140) reducer**: unlike
  `phase140_of_nonsingular` (which routes through the `Lin`/`κ_ρ`/`ε_ρ`/`N(κ,ε)`-interpolation of
  `lemma_8_5`), this reducer consumes the per-`ρ` **phase-obstruction identity**

  `2·|D_T| · #(central red_T image)(ρ) = |V| · (|V| + G0 · Σ_ζ phaseSign(ζ, ρ))`

  — exactly the shape the paper's proof of Prop 8.9 produces from (126)+(135) before summing
  over `ρ` (pp. 42–43), with the phase family and `μ`-slot as in the c1s-repaired engine
  (`μ_total = |V|·μ₀`).  The master-count file (`GQ2/VLiftCount.lean`) supplies `hMobst`.

Everything is source-generic; all std-3.
-/

namespace GQ2

namespace SectionEight

open QuadraticFp2 ContCoh

/-! ## The coboundary indicator `ι_Γ` -/

section Iota

variable {Γ : Type} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
variable [DistribMulAction Γ (ZMod 2)] [ContinuousSMul Γ (ZMod 2)]

/-- **The coboundary indicator** `ι_Γ` on `𝔽₂`-valued 2-cochains: `0` iff the cochain is a
continuous coboundary.  On cocycles, with `#H²(Γ,𝔽₂) = 2`, this is the composite of the class
map with the unique isomorphism `H²(Γ,𝔽₂) ≅ 𝔽₂` (`iotaB_add`). -/
noncomputable def iotaB (φ : Γ × Γ → ZMod 2) : ZMod 2 :=
  letI := Classical.dec (φ ∈ B2 Γ (ZMod 2))
  if φ ∈ B2 Γ (ZMod 2) then 0 else 1

omit [IsTopologicalGroup Γ] [ContinuousSMul Γ (ZMod 2)] in
theorem iotaB_eq_zero_iff {φ : Γ × Γ → ZMod 2} :
    iotaB φ = 0 ↔ φ ∈ B2 Γ (ZMod 2) := by
  unfold iotaB
  split_ifs with h
  · exact ⟨fun _ => h, fun _ => rfl⟩
  · exact ⟨fun h1 => absurd h1 one_ne_zero, fun hmem => absurd hmem h⟩

omit [IsTopologicalGroup Γ] [ContinuousSMul Γ (ZMod 2)] in
theorem iotaB_of_mem_B2 {φ : Γ × Γ → ZMod 2} (h : φ ∈ B2 Γ (ZMod 2)) : iotaB φ = 0 :=
  iotaB_eq_zero_iff.mpr h

omit [IsTopologicalGroup Γ] [ContinuousSMul Γ (ZMod 2)] in
/-- The `H²`-class of a cocycle vanishes iff its underlying cochain is a coboundary. -/
theorem H2mk_eq_zero_iff (φ : Z2 Γ (ZMod 2)) :
    H2mk Γ (ZMod 2) φ = 0 ↔ (φ : Γ × Γ → ZMod 2) ∈ B2 Γ (ZMod 2) := by
  rw [show H2mk Γ (ZMod 2) φ = 0 ↔ φ ∈ (B2 Γ (ZMod 2)).addSubgroupOf (Z2 Γ (ZMod 2)) from
    QuotientAddGroup.eq_zero_iff φ]
  exact AddSubgroup.mem_addSubgroupOf

omit [IsTopologicalGroup Γ] [ContinuousSMul Γ (ZMod 2)] in
/-- **Additivity of `ι_Γ` on cocycles** (`#H²(Γ,𝔽₂) = 2`): the indicator is the unique
isomorphism `H² ≅ 𝔽₂` composed with the class map, hence additive.  The `hH2` hypothesis is the
per-source `#H²(Γ,𝔽₂) = 2` count (`lemma_8_2`-adjacent; threaded to the d6e residue list). -/
theorem iotaB_add (hH2 : Nat.card (H2 Γ (ZMod 2)) = 2) {φ ψ : Γ × Γ → ZMod 2}
    (hφ : φ ∈ Z2 Γ (ZMod 2)) (hψ : ψ ∈ Z2 Γ (ZMod 2)) :
    iotaB (φ + ψ) = iotaB φ + iotaB ψ := by
  classical
  -- nonzero classes in a 2-element group coincide
  haveI : Finite (H2 Γ (ZMod 2)) := Nat.finite_of_card_ne_zero (by omega)
  haveI : Fintype (H2 Γ (ZMod 2)) := Fintype.ofFinite _
  have huniq : ∀ x y : H2 Γ (ZMod 2), x ≠ 0 → y ≠ 0 → x = y := by
    intro x y hx hy
    by_contra hxy
    have hcard3 : ({0, x, y} : Finset (H2 Γ (ZMod 2))).card = 3 := by
      rw [Finset.card_insert_of_notMem (by simp [Ne.symm hx, Ne.symm hy]),
        Finset.card_insert_of_notMem (by simp [hxy]), Finset.card_singleton]
    have hle : ({0, x, y} : Finset (H2 Γ (ZMod 2))).card ≤ Fintype.card (H2 Γ (ZMod 2)) :=
      Finset.card_le_univ _
    rw [hcard3, ← Nat.card_eq_fintype_card, hH2] at hle
    omega
  by_cases h1 : φ ∈ B2 Γ (ZMod 2) <;> by_cases h2 : ψ ∈ B2 Γ (ZMod 2)
  · rw [iotaB_of_mem_B2 h1, iotaB_of_mem_B2 h2, iotaB_of_mem_B2 (AddSubgroup.add_mem _ h1 h2),
      add_zero]
  · have hsum : φ + ψ ∉ B2 Γ (ZMod 2) := fun hmem => by
      have := AddSubgroup.sub_mem _ hmem h1
      rw [add_sub_cancel_left] at this
      exact h2 this
    rw [iotaB_of_mem_B2 h1, iotaB, if_neg hsum, iotaB, if_neg h2, zero_add]
  · have hsum : φ + ψ ∉ B2 Γ (ZMod 2) := fun hmem => by
      have := AddSubgroup.sub_mem _ hmem h2
      rw [add_sub_cancel_right] at this
      exact h1 this
    rw [iotaB_of_mem_B2 h2, iotaB, if_neg hsum, iotaB, if_neg h1, add_zero]
  · -- both classes nonzero, hence equal; their sum is zero
    have hx : H2mk Γ (ZMod 2) ⟨φ, hφ⟩ ≠ 0 := fun h0 => h1 ((H2mk_eq_zero_iff _).mp h0)
    have hy : H2mk Γ (ZMod 2) ⟨ψ, hψ⟩ ≠ 0 := fun h0 => h2 ((H2mk_eq_zero_iff _).mp h0)
    have hxy := huniq _ _ hx hy
    have hyy : H2mk Γ (ZMod 2) ⟨ψ, hψ⟩ + H2mk Γ (ZMod 2) ⟨ψ, hψ⟩ = 0 := by
      by_contra hne
      have hcollapse := huniq _ _ hne hy
      have h0 : H2mk Γ (ZMod 2) ⟨ψ, hψ⟩ = 0 := by
        have := congrArg (· - H2mk Γ (ZMod 2) ⟨ψ, hψ⟩) hcollapse
        simpa using this
      exact hy h0
    have hsum0 : H2mk Γ (ZMod 2) (⟨φ, hφ⟩ + ⟨ψ, hψ⟩) = 0 := by
      have : H2mk Γ (ZMod 2) (⟨φ, hφ⟩ + ⟨ψ, hψ⟩)
          = H2mk Γ (ZMod 2) ⟨φ, hφ⟩ + H2mk Γ (ZMod 2) ⟨ψ, hψ⟩ := map_add _ _ _
      rw [this, hxy, hyy]
    have hmem : φ + ψ ∈ B2 Γ (ZMod 2) := (H2mk_eq_zero_iff _).mp hsum0
    rw [iotaB_of_mem_B2 hmem, iotaB, if_neg h1, iotaB, if_neg h2]
    decide

end Iota

/-! ## Pullback of finite-group 2-cochains -/

section Pull

variable {Γ : Type} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
variable [DistribMulAction Γ (ZMod 2)] [ContinuousSMul Γ (ZMod 2)]
variable {C0 : Type} [Group C0] [TopologicalSpace C0] [DiscreteTopology C0]

/-- Pullback of a finite-group 2-cochain along (the square of) a map. -/
def pullCoc (f : Γ → C0) (δ : C0 × C0 → ZMod 2) : Γ × Γ → ZMod 2 :=
  fun p => δ (f p.1, f p.2)

omit [Group Γ] [IsTopologicalGroup Γ] [DistribMulAction Γ (ZMod 2)]
  [ContinuousSMul Γ (ZMod 2)] [Group C0] in
theorem pullCoc_continuous {f : Γ → C0} (hf : Continuous f) (δ : C0 × C0 → ZMod 2) :
    Continuous (pullCoc f δ) :=
  (continuous_of_discreteTopology (f := fun q : C0 × C0 => δ q)).comp
    ((hf.comp continuous_fst).prodMk (hf.comp continuous_snd))

omit [IsTopologicalGroup Γ] [ContinuousSMul Γ (ZMod 2)] in
/-- The pullback of a raw 2-cocycle along a continuous hom is a continuous 2-cocycle. -/
theorem pullCoc_mem_Z2 (htriv : ∀ (γ : Γ) (m : ZMod 2), γ • m = m)
    (f : ContinuousMonoidHom Γ C0) {δ : C0 × C0 → ZMod 2}
    (hcoc : ∀ g h k : C0, δ (h, k) + δ (g, h * k) = δ (g * h, k) + δ (g, h)) :
    pullCoc (⇑f) δ ∈ Z2 Γ (ZMod 2) := by
  refine mem_Z2_iff.mpr ⟨pullCoc_continuous f.continuous_toFun δ, fun g h k => ?_⟩
  rw [htriv]
  show δ (f h, f k) + δ (f g, f (h * k)) = δ (f (g * h), f k) + δ (f g, f h)
  rw [map_mul, map_mul]
  exact hcoc (f g) (f h) (f k)


end Pull

/-! ## Central-cover z-power calculus and the lifting criterion -/

section CoverLift

variable {Y0 : Type} [Group Y0] [Finite Y0]

/-- `p z = 1` for any central double cover. -/
theorem CentralCover.p_z_eq_one (CC : CentralCover Y0) : CC.p CC.z = 1 :=
  MonoidHom.mem_ker.mp (by rw [CC.ker_eq]; exact Subgroup.mem_zpowers _)

/-- Kernel dichotomy for a central double cover: `ker p = {1, z}`. -/
theorem CentralCover.ker_dichotomy (CC : CentralCover Y0) {x : CC.cover}
    (hx : x ∈ CC.p.ker) : x = 1 ∨ x = CC.z := by
  rw [CC.ker_eq, Subgroup.mem_zpowers_iff] at hx
  obtain ⟨n, rfl⟩ := hx
  have hz2 : CC.z ^ (2 : ℤ) = 1 := by
    rw [show (2 : ℤ) = 1 + 1 from rfl, zpow_add, zpow_one, CC.z_sq]
  rcases Int.even_or_odd n with ⟨k, hk⟩ | ⟨k, hk⟩
  · left; rw [hk, ← two_mul, zpow_mul, hz2, one_zpow]
  · right; rw [hk, zpow_add, zpow_mul, hz2, one_zpow, one_mul, zpow_one]

/-- `z`-powers by `𝔽₂`-exponents add. -/
theorem CentralCover.z_pow_val_add (CC : CentralCover Y0) (a b : ZMod 2) :
    CC.z ^ (a + b).val = CC.z ^ a.val * CC.z ^ b.val := by
  rcases (show ∀ x : ZMod 2, x = 0 ∨ x = 1 from by decide) a with rfl | rfl <;>
    rcases (show ∀ x : ZMod 2, x = 0 ∨ x = 1 from by decide) b with rfl | rfl
  · show CC.z ^ 0 = CC.z ^ 0 * CC.z ^ 0
    rw [pow_zero, one_mul]
  · show CC.z ^ 1 = CC.z ^ 0 * CC.z ^ 1
    rw [pow_zero, one_mul]
  · show CC.z ^ 1 = CC.z ^ 1 * CC.z ^ 0
    rw [pow_zero, mul_one]
  · show CC.z ^ 0 = CC.z ^ 1 * CC.z ^ 1
    rw [pow_zero, pow_one]
    exact CC.z_sq.symm

/-- `z`-powers are central. -/
theorem CentralCover.z_pow_comm (CC : CentralCover Y0) (n : ℕ) (x : CC.cover) :
    CC.z ^ n * x = x * CC.z ^ n := by
  have hc : Commute CC.z x := CC.central x
  exact (hc.pow_left n).eq

/-- `𝔽₂`-exponents of `z` are determined: `z^{a} = z^{b} → a = b`. -/
theorem CentralCover.z_pow_val_inj (CC : CentralCover Y0) {a b : ZMod 2}
    (h : CC.z ^ a.val = CC.z ^ b.val) : a = b := by
  by_contra hne
  rcases (show ∀ x : ZMod 2, x = 0 ∨ x = 1 from by decide) a with rfl | rfl <;>
    rcases (show ∀ x : ZMod 2, x = 0 ∨ x = 1 from by decide) b with rfl | rfl
  · exact hne rfl
  · rw [show ((0 : ZMod 2)).val = 0 from rfl, show ((1 : ZMod 2)).val = 1 from rfl,
      pow_zero, pow_one] at h
    exact CC.z_ne h.symm
  · rw [show ((0 : ZMod 2)).val = 0 from rfl, show ((1 : ZMod 2)).val = 1 from rfl,
      pow_zero, pow_one] at h
    exact CC.z_ne h
  · exact hne rfl

section LiftIff

variable {Γ : Type} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
variable [DistribMulAction Γ (ZMod 2)] [ContinuousSMul Γ (ZMod 2)]
variable {Y0 : Type} [Group Y0] [TopologicalSpace Y0] [DiscreteTopology Y0] [Finite Y0]

omit [IsTopologicalGroup Γ] [ContinuousSMul Γ (ZMod 2)] in
/-- **The central-cover lifting criterion**: for a central double cover of `Y₀` equipped with a
set-section of multiplication defect `δ` (`s c · s d = z^{δ(c,d)} · s(cd)`), a continuous hom
`f : Γ → Y₀` lifts through the cover iff the pulled-back defect `f^*δ` is a continuous
coboundary.  (`centralCoverOfCocycle_exists_section` supplies such a section, with defect the
defining cocycle, for the twisted-product phase covers.) -/
theorem centralCover_lift_iff (htriv : ∀ (γ : Γ) (m : ZMod 2), γ • m = m)
    (CC : CentralCover Y0) (s : Y0 → CC.cover) (hs : ∀ c, CC.p (s c) = c)
    (δ : Y0 × Y0 → ZMod 2)
    (hdef : ∀ c d, s c * s d = CC.z ^ (δ (c, d)).val * s (c * d))
    (f : ContinuousMonoidHom Γ Y0) :
    (∃ g : ContinuousMonoidHom Γ CC.cover, ∀ γ : Γ, CC.p (g γ) = f γ) ↔
      pullCoc (⇑f) δ ∈ B2 Γ (ZMod 2) := by
  constructor
  · -- a lift `g` differs from `s ∘ f` by a kernel-valued cochain trivializing the defect
    rintro ⟨g, hg⟩
    classical
    set w : Γ → ZMod 2 := fun γ => if g γ * (s (f γ))⁻¹ = 1 then 0 else 1 with hw
    have hker : ∀ γ, g γ * (s (f γ))⁻¹ ∈ CC.p.ker := by
      intro γ
      rw [MonoidHom.mem_ker, map_mul, map_inv, hg, hs, mul_inv_cancel]
    have hrec : ∀ γ, g γ = CC.z ^ (w γ).val * s (f γ) := by
      intro γ
      rcases CC.ker_dichotomy (hker γ) with h1 | hz
      · have heq : g γ = s (f γ) := by
          have := congrArg (· * s (f γ)) h1
          simpa [mul_assoc] using this
        have hwγ : w γ = 0 := if_pos h1
        rw [hwγ, show ((0 : ZMod 2)).val = 0 from rfl, pow_zero, one_mul, heq]
      · have heq : g γ = CC.z * s (f γ) := by
          have := congrArg (· * s (f γ)) hz
          simpa [mul_assoc] using this
        have hwγ : w γ = 1 := if_neg (fun h => CC.z_ne (hz.symm.trans h))
        rw [hwγ, show ((1 : ZMod 2)).val = 1 from rfl, pow_one, heq]
    refine ⟨w, ?_, ?_⟩
    · -- continuity: `w` factors through the discrete cover
      have : w = (fun x : CC.cover × CC.cover => if x.1 * x.2⁻¹ = 1 then (0 : ZMod 2) else 1)
          ∘ (fun γ => (g γ, s (f γ))) := rfl
      rw [this]
      exact continuous_of_discreteTopology.comp
        (g.continuous_toFun.prodMk ((continuous_of_discreteTopology
          (f := fun c : Y0 => s c)).comp f.continuous_toFun))
    · -- `∂w = f^*δ`: compare the two expansions of `g(γδ)`
      funext p
      obtain ⟨γ, d⟩ := p
      have hmul : g (γ * d) = g γ * g d := map_mul g γ d
      rw [hrec (γ * d), hrec γ, hrec d] at hmul
      have hexp : CC.z ^ (w γ).val * s (f γ) * (CC.z ^ (w d).val * s (f d))
          = CC.z ^ (w γ + w d + δ (f γ, f d)).val * s (f (γ * d)) := by
        calc CC.z ^ (w γ).val * s (f γ) * (CC.z ^ (w d).val * s (f d))
            = CC.z ^ (w γ).val * CC.z ^ (w d).val * (s (f γ) * s (f d)) := by
              rw [show CC.z ^ (w γ).val * s (f γ) * (CC.z ^ (w d).val * s (f d))
                  = CC.z ^ (w γ).val * (s (f γ) * CC.z ^ (w d).val) * s (f d) from by group,
                ← CC.z_pow_comm (w d).val (s (f γ))]
              group
          _ = CC.z ^ (w γ).val * CC.z ^ (w d).val
                * (CC.z ^ (δ (f γ, f d)).val * s (f γ * f d)) := by rw [hdef]
          _ = CC.z ^ (w γ + w d + δ (f γ, f d)).val * s (f (γ * d)) := by
              rw [CC.z_pow_val_add (w γ + w d) (δ (f γ, f d)), CC.z_pow_val_add (w γ) (w d),
                map_mul]
              group
      rw [hexp] at hmul
      have hzeq : CC.z ^ (w (γ * d)).val = CC.z ^ (w γ + w d + δ (f γ, f d)).val :=
        mul_right_cancel hmul
      have hval : w (γ * d) = w γ + w d + δ (f γ, f d) := CC.z_pow_val_inj hzeq
      show γ • w d - w (γ * d) + w γ = δ (f γ, f d)
      rw [htriv, hval]
      have hchar : ∀ a b c : ZMod 2, a - (a + b + c) + b = c := by decide
      rw [show w γ + w d + δ (f γ, f d) = w d + w γ + δ (f γ, f d) from by ring]
      exact hchar (w d) (w γ) (δ (f γ, f d))
  · -- a trivializing cochain builds the lift `γ ↦ z^{w γ} · s(f γ)`
    rintro ⟨w, hwc, hw⟩
    have hwval : ∀ γ d : Γ, w (γ * d) = w γ + w d + δ (f γ, f d) := by
      intro γ d
      have hthis : γ • w d - w (γ * d) + w γ = δ (f γ, f d) := congrFun hw (γ, d)
      rw [htriv] at hthis
      have hchar : ∀ a b c D : ZMod 2, a - b + c = D → b = c + a + D := by decide
      exact hchar (w d) (w (γ * d)) (w γ) (δ (f γ, f d)) hthis
    refine ⟨⟨MonoidHom.mk' (fun γ => CC.z ^ (w γ).val * s (f γ)) (fun γ d => ?_), ?_⟩,
      fun γ => ?_⟩
    · calc CC.z ^ (w (γ * d)).val * s (f (γ * d))
          = CC.z ^ (w γ + w d + δ (f γ, f d)).val * s (f (γ * d)) := by rw [hwval]
        _ = CC.z ^ (w γ).val * CC.z ^ (w d).val
              * (CC.z ^ (δ (f γ, f d)).val * s (f γ * f d)) := by
            rw [CC.z_pow_val_add (w γ + w d) (δ (f γ, f d)), CC.z_pow_val_add (w γ) (w d),
              map_mul]
            group
        _ = CC.z ^ (w γ).val * CC.z ^ (w d).val * (s (f γ) * s (f d)) := by rw [← hdef]
        _ = CC.z ^ (w γ).val * s (f γ) * (CC.z ^ (w d).val * s (f d)) := by
            rw [show CC.z ^ (w γ).val * CC.z ^ (w d).val * (s (f γ) * s (f d))
                = CC.z ^ (w γ).val * (CC.z ^ (w d).val * s (f γ)) * s (f d) from by group,
              CC.z_pow_comm (w d).val (s (f γ))]
            group
    · show Continuous fun γ => CC.z ^ (w γ).val * s (f γ)
      have : (fun γ => CC.z ^ (w γ).val * s (f γ))
          = (fun x : ZMod 2 × Y0 => CC.z ^ x.1.val * s x.2) ∘ (fun γ => (w γ, f γ)) := rfl
      rw [this]
      exact continuous_of_discreteTopology.comp (hwc.prodMk f.continuous_toFun)
    · show CC.p (CC.z ^ (w γ).val * s (f γ)) = f γ
      rw [map_mul, map_pow, CC.p_z_eq_one, one_pow, one_mul, hs]

open AffineTLift in
open scoped Classical in
omit [IsTopologicalGroup Γ] [ContinuousSMul Γ (ZMod 2)] in
/-- **The sign bridge** (P-16d6e supply): for the twisted-product phase cover of a normalized
raw 2-cocycle `δ`, the master count's `±1` (`sign ι_Γ(f^*δ)`) IS the signed liftability
through the cover — `phaseSign`'s if-form at `f`.  Composes `centralCover_lift_iff` with the
canonical section of `centralCoverOfCocycle` and `ι_Γ`'s defining dichotomy. -/
theorem sign_iotaB_pullCoc_eq_lift_sign (htriv : ∀ (γ : Γ) (m : ZMod 2), γ • m = m)
    (δ : Y0 × Y0 → ZMod 2)
    (hcoc : ∀ g h k : Y0, δ (h, k) + δ (g, h * k) = δ (g * h, k) + δ (g, h))
    (hl : ∀ c : Y0, δ (1, c) = 0) (hr : ∀ c : Y0, δ (c, 1) = 0)
    (f : ContinuousMonoidHom Γ Y0) :
    sign (iotaB (pullCoc (⇑f) δ))
      = if ∃ g : ContinuousMonoidHom Γ (centralCoverOfCocycle δ hcoc hl hr).cover,
            ∀ γ : Γ, (centralCoverOfCocycle δ hcoc hl hr).p (g γ) = f γ
          then 1 else -1 := by
  classical
  obtain ⟨s, hs, -, hdef⟩ := centralCoverOfCocycle_exists_section δ hcoc hl hr
  have hiff := centralCover_lift_iff htriv (centralCoverOfCocycle δ hcoc hl hr) s hs δ hdef f
  by_cases hmem : pullCoc (⇑f) δ ∈ B2 Γ (ZMod 2)
  · rw [if_pos (hiff.mpr hmem), iotaB_of_mem_B2 hmem]
    decide
  · rw [if_neg fun hex => hmem (hiff.mp hex)]
    have h1 : iotaB (pullCoc (⇑f) δ) = 1 := by rw [iotaB, if_neg hmem]
    rw [h1]
    decide

end LiftIff

end CoverLift

/-! ## The signed phase-liftability count (141) -/

section PhaseSign

variable {H E : Type} [Group H] [TopologicalSpace H] [DiscreteTopology H] [Finite H]
  [CommGroup E] [TopologicalSpace E] [DiscreteTopology E] [Finite E]
variable {Γ : Type} [Group Γ] [TopologicalSpace Γ]
variable {Y : Type} [Group Y] [TopologicalSpace Y] [DiscreteTopology Y] [Finite Y]
variable {T : MarkedTarget H E Y} {Blk : SectionSeven.MinimalBlock T.LY}
  (RF : RecursionFrame T Blk)
variable (b : ContinuousMonoidHom Γ ↥boundarySubgroup) (F : BoundaryFrame H E)

open scoped Classical in
/-- The **signed liftability** of a lower exact-image map through a phase cover: `+1` when a
lift exists, `−1` otherwise — (141)'s summand `(−1)^{ι_Γ(ρ^*ζ)}` in predicate form. -/
noncomputable def phaseSign (Cζ : CentralCover RF.YC) (ρ : BoundaryLifts b F RF.TC) : ℤ :=
  if ∃ g : ContinuousMonoidHom Γ Cζ.cover, ∀ γ : Γ, Cζ.p (g γ) = ρ.1.1 γ then 1 else -1

omit [TopologicalSpace Y] [DiscreteTopology Y] in
/-- **(141)**: the signed liftability sum over the lower exact-image maps is
`2·n_{Γ,0}(ζ) − e_Γ(C)`. -/
theorem sum_phaseSign [Fintype (BoundaryLifts b F RF.TC)] (Cζ : CentralCover RF.YC) :
    ∑ᶠ ρ : BoundaryLifts b F RF.TC, phaseSign RF b F Cζ ρ
      = 2 * (RF.nPhase b F Cζ : ℤ) - (exactImageCount b F RF.TC : ℤ) := by
  classical
  rw [finsum_eq_sum_of_fintype]
  have hterm : ∀ ρ : BoundaryLifts b F RF.TC, phaseSign RF b F Cζ ρ
      = 2 * (if (∃ g : ContinuousMonoidHom Γ Cζ.cover, ∀ γ : Γ, Cζ.p (g γ) = ρ.1.1 γ)
          then (1 : ℤ) else 0) - 1 := by
    intro ρ
    unfold phaseSign
    split_ifs <;> ring
  rw [Finset.sum_congr rfl fun ρ _ => hterm ρ, Finset.sum_sub_distrib, ← Finset.mul_sum,
    Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
  congr 1
  · congr 1
    rw [Finset.sum_boole]
    rw [show RF.nPhase b F Cζ = Nat.card {f : BoundaryLifts b F RF.TC //
        ∃ g : ContinuousMonoidHom Γ Cζ.cover, ∀ γ : Γ, Cζ.p (g γ) = f.1.1 γ} from rfl,
      Nat.card_eq_fintype_card, Fintype.card_subtype]
  · rw [show exactImageCount b F RF.TC = Nat.card (BoundaryLifts b F RF.TC) from rfl,
      Nat.card_eq_fintype_card]

end PhaseSign

/-! ## The paper-faithful (140) reducer -/

variable {H E : Type} [Group H] [TopologicalSpace H] [DiscreteTopology H] [Finite H]
  [CommGroup E] [TopologicalSpace E] [DiscreteTopology E] [Finite E]

open AffineTLift CentralObstruction in
/-- **The (140) display from per-`ρ` phase-obstruction data** (P-16d6c, paper-faithful form).
Unlike `phase140_of_nonsingular` (which interpolates through `lemma_8_5`'s
`Lin`/`κ_ρ`/`ε_ρ`/`N(κ,ε)` data), this reducer consumes the identity the paper's Prop 8.9 proof
actually produces per lower map (pp. 42–43, (126)+(135) before the `ρ`-sum):

  `2·|D_T| · #(central red_T image)(ρ) = |V| · (|V| + G0 · Σ_ζ (±1)_{ζ,ρ})`,

with `(±1)_{ζ,ρ} = phaseSign (phase ζ) ρ` the signed liftability through the phase cover.
Combined with the `T`-torsor factoring (`zBC_eq_mu_mul_reductionCount`, needing μ-independence
`hμ`) and the (141) count (`sum_phaseSign`), the boxed (140) follows with the c1s multiplicity
slot `μ_total = |V|·μ₀`.  The master-count file supplies `hMobst`. -/
theorem phase140_of_phaseObstruction {Γ : Type} [Group Γ] [TopologicalSpace Γ]
    [IsTopologicalGroup Γ] [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    [DistribMulAction Γ (ZMod 2)] [ContinuousSMul Γ (ZMod 2)]
    {Y : Type} [Group Y] [TopologicalSpace Y] [DiscreteTopology Y] [Finite Y]
    {T : MarkedTarget H E Y} {Blk : SectionSeven.MinimalBlock T.LY} (RF : RecursionFrame T Blk)
    (b : ContinuousMonoidHom Γ ↥boundarySubgroup) (F : BoundaryFrame H E)
    (μ₀ : ℕ) (G0 : ℤ) (DT : Type) [Fintype DT] (phase : DT → CentralCover RF.YC)
    (l : RF.DR) (h : l ≠ RF.zeroDR)
    (D : RadicalCoverData RF.YB) (hD : D.M = RF.MB) (hC : D.C = RF.scalarCover l h)
    (Dsc : Descent D) (htriv : ∀ (γ : Γ) (m : ZMod 2), γ • m = m)
    (hfg : ∃ s : Finset Γ, (Subgroup.closure (s : Set Γ)).topologicalClosure = ⊤)
    [Fintype (BoundaryLifts b F RF.TC)]
    (cardV : ℕ) (hWV : cardV = Nat.card ↥RF.MB / Nat.card ↥RF.TBsub)
    (hμ : ∀ ρ : BoundaryLifts b F RF.TC, Nat.card (TCocycle D (RF.rhoPrime b F D hD ρ)) = μ₀)
    (hMobst : ∀ ρ : BoundaryLifts b F RF.TC,
      2 * (Nat.card DT : ℤ) * (Nat.card ↥(Set.range
          (fun f : {f : MLifts D (RF.rhoPrime b F D hD ρ) // f.Central} =>
            redT (RF.rhoPrime b F D hD ρ) f.1)) : ℤ)
        = (cardV : ℤ) * ((cardV : ℤ)
            + G0 * ∑ᶠ ζ : DT, phaseSign RF b F (phase ζ) ρ)) :
    2 * (Nat.card DT : ℤ) * RF.zBC b F l h
      = (cardV * μ₀ : ℕ)
          * ((Nat.card ↥RF.MB / Nat.card ↥RF.TBsub : ℕ) * exactImageCount b F RF.TC
            + G0 * ∑ᶠ ζ : DT, (2 * (RF.nPhase b F (phase ζ) : ℤ)
                - (exactImageCount b F RF.TC : ℤ))) := by
  classical
  -- the `T`-torsor factoring
  have hfib := zBC_eq_mu_mul_reductionCount RF b F l h D hD hC Dsc htriv hfg μ₀ hμ
  set img : BoundaryLifts b F RF.TC → ℕ := fun ρ => Nat.card ↥(Set.range
    (fun f : {f : MLifts D (RF.rhoPrime b F D hD ρ) // f.Central} =>
      redT (RF.rhoPrime b F D hD ρ) f.1)) with himg
  have hz : (RF.zBC b F l h : ℤ) = (μ₀ : ℤ) * ∑ ρ, (img ρ : ℤ) := by
    rw [hfib, finsum_eq_sum_of_fintype]
    push_cast
    ring
  have hexact : (exactImageCount b F RF.TC : ℤ)
      = (Fintype.card (BoundaryLifts b F RF.TC) : ℤ) := by
    rw [show exactImageCount b F RF.TC = Nat.card (BoundaryLifts b F RF.TC) from rfl,
      Nat.card_eq_fintype_card]
  -- the (141) evaluation of the swapped inner sum
  have hswap : (∑ ζ : DT, ∑ ρ, phaseSign RF b F (phase ζ) ρ)
      = ∑ᶠ ζ : DT, (2 * (RF.nPhase b F (phase ζ) : ℤ)
          - (exactImageCount b F RF.TC : ℤ)) := by
    rw [finsum_eq_sum_of_fintype]
    refine Finset.sum_congr rfl fun ζ _ => ?_
    rw [← sum_phaseSign RF b F (phase ζ), finsum_eq_sum_of_fintype]
  -- sum the per-ρ identity and swap the double sum
  have hsum : 2 * (Nat.card DT : ℤ) * ∑ ρ, (img ρ : ℤ)
      = (cardV : ℤ) * ((exactImageCount b F RF.TC : ℤ) * cardV
          + G0 * ∑ᶠ ζ : DT, (2 * (RF.nPhase b F (phase ζ) : ℤ)
              - (exactImageCount b F RF.TC : ℤ))) := by
    calc 2 * (Nat.card DT : ℤ) * ∑ ρ, (img ρ : ℤ)
        = ∑ ρ, 2 * (Nat.card DT : ℤ) * (img ρ : ℤ) := by rw [Finset.mul_sum]
      _ = ∑ ρ, (cardV : ℤ) * ((cardV : ℤ)
            + G0 * ∑ᶠ ζ : DT, phaseSign RF b F (phase ζ) ρ) :=
          Finset.sum_congr rfl fun ρ _ => hMobst ρ
      _ = (cardV : ℤ) * (∑ ρ, ((cardV : ℤ)
            + G0 * ∑ ζ : DT, phaseSign RF b F (phase ζ) ρ)) := by
          rw [← Finset.mul_sum]
          exact congrArg _ (Finset.sum_congr rfl fun ρ _ => by rw [finsum_eq_sum_of_fintype])
      _ = (cardV : ℤ) * ((exactImageCount b F RF.TC : ℤ) * cardV
            + G0 * ∑ ζ : DT, ∑ ρ, phaseSign RF b F (phase ζ) ρ) := by
          rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, ← Finset.mul_sum,
            Finset.sum_comm, hexact, nsmul_eq_mul]
      _ = (cardV : ℤ) * ((exactImageCount b F RF.TC : ℤ) * cardV
            + G0 * ∑ᶠ ζ : DT, (2 * (RF.nPhase b F (phase ζ) : ℤ)
                - (exactImageCount b F RF.TC : ℤ))) := by rw [hswap]
  -- assemble
  have hVcast : ((Nat.card ↥RF.MB / Nat.card ↥RF.TBsub : ℕ) : ℤ) = (cardV : ℤ) := by
    exact_mod_cast congrArg (Nat.cast (R := ℤ)) hWV.symm
  rw [hz, show 2 * (Nat.card DT : ℤ) * ((μ₀ : ℤ) * ∑ ρ, (img ρ : ℤ))
      = (μ₀ : ℤ) * (2 * (Nat.card DT : ℤ) * ∑ ρ, (img ρ : ℤ)) from by ring, hsum, hVcast,
    show ((cardV * μ₀ : ℕ) : ℤ) = (cardV : ℤ) * (μ₀ : ℤ) from by push_cast; ring]
  ring

end SectionEight

end GQ2
