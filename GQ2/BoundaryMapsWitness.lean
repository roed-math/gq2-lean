import GQ2.BoundaryConstruction
import GQ2.LocalMarked
import GQ2.Prop32

/-!
# `prop_3_14 : Nonempty BoundaryMaps` — the eq. (27) boundary data  (ticket P-25)

The third and last orphaned `SectionThreeMarked.lean` sorry: the full 21-field `BoundaryMaps`
bundle (`GQ2/BoundaryFrame.lean`), i.e. tame + maximal-pro-2 quotient maps for **both** sources
`Γ_A` and `G_{ℚ₂}`, `ν`-compatible, jointly surjective onto the fibred boundary
`∂bd = T_tame ×_{ℤ₂} Π`.

## Structure of the construction

Everything reduces to a small kit:

* **`fiberProductExists`** (pure algebra) — surjectivity onto a fibred product `A ×_C B` from
  `f : G ↠ A` surjective, the square `α∘f = β∘h` commuting, and `h(ker f) ⊇ ker β`.
* **`proPKernel_image_ge`** — for a surjection `φ : G ↠ H` of profinite groups,
  `proPKernel p H ⊆ φ(proPKernel p G)`.
* **`ker_nuT_le_proPKernel`** — `ker ν_t ⊆ proPKernel 2 T_tame`: `ν_t : T_tame ↠ ℤ₂` is (contained
  in) the maximal pro-2 quotient, because the tame relation `τ^σ = τ²` forces `τ ↦ 1` in every
  finite 2-group quotient.

With these, the kernel hypothesis of `fiberProductExists` (`h(ker f) ⊇ ker β`) becomes
`ker ν₂ ⊆ pro2X(ker tameX)`, discharged uniformly by `hker_uniform`.

* `Γ_A` side: `tameA = φ_A` (P-09), `pro2A = φ_Π` (P-25 `prop_3_10_gammaA`), `compatA` by density
  on the four marked generators.
* `G_{ℚ₂}` side: `tameF` from `prop_3_2_local` (B10 `LocalTameQuotient` + Lemma 3.3 maximality),
  `pro2F` from `prop_3_10_local_marked` (P-25) with `R = GQ2.localReciprocity` (B5).

## The one arithmetic gap: `compatF` (`tame_reciprocity`)

`compatF : ∀ g, ν_t(tameF g) = ν₂(pro2F g)` is the internal tame-vs-pro-2 compatibility on
`G_{ℚ₂}`.  Via `prop_3_10_local_marked` it reduces to the **tame reciprocity** statement
`ι(ν_t(tameF g)) = ν_ur(toAb g)` — the tame quotient's unramified character equals `ν_ur`.
The B10 tame-quotient bundle carries **no** orientation of its `σ` against Frobenius (its `equiv`
is an unoriented iso `G/W ≅ T_tame`), and B5's `ν_ur` is defined via reciprocity; nothing in the
current axioms ties the two together.  This is genuine arithmetic content (wild inertia is
unramified-trivial), isolated here as `tame_reciprocity` and left as the single `sorry`.
Per the design note (`docs/section3-extraction.md`, "marked half"), `compat…` carries no
downstream `ν_ur`-anchor, so this is the natural minimal gap; discharging it cleanly wants a
`tame_reciprocity` axiom (census decision, deferred to the user).
-/

namespace GQ2

namespace SectionThree

open scoped Classical

/-! ## The pure-algebra fibred-product surjectivity kit -/

/-- **Fibred-product surjectivity (algebra).**  If `f` is surjective, the square commutes
(`α ∘ f = β ∘ h`), and `h` maps `ker f` onto `ker β`, then every fibred-product point `(t, p)`
with `α t = β p` is `(f g, h g)` for some `g`. -/
theorem fiberProductExists
    {G A B C : Type*} [Group G] [Group A] [Group B] [Group C]
    (α : A →* C) (β : B →* C) (f : G →* A) (h : G →* B)
    (hf : Function.Surjective f)
    (hcompat : ∀ g, α (f g) = β (h g))
    (hker : ∀ b : B, β b = 1 → ∃ g : G, f g = 1 ∧ h g = b)
    (t : A) (p : B) (hmem : α t = β p) :
    ∃ g : G, f g = t ∧ h g = p := by
  obtain ⟨g₀, hg₀⟩ := hf t
  have hb1 : β ((h g₀)⁻¹ * p) = 1 := by
    rw [map_mul, map_inv, ← hcompat, hg₀, ← hmem, inv_mul_cancel]
  obtain ⟨k, hk1, hk2⟩ := hker ((h g₀)⁻¹ * p) hb1
  refine ⟨g₀ * k, ?_, ?_⟩
  · rw [map_mul, hk1, mul_one, hg₀]
  · rw [map_mul, hk2, mul_inv_cancel_left]

/-! ## The two structural lemmas (see module docstring) -/

/-- **Surjective image of the pro-`p` kernel.**  For a surjection `φ : G ↠ H` of profinite
groups, `proPKernel p H ⊆ φ(proPKernel p G)`: `H / φ(proPKernel p G)` is a quotient of the pro-`p`
group `G(p)`, hence pro-`p`, so it kills `proPKernel p H`. -/
theorem proPKernel_image_ge {p : ℕ} {G H : Type*}
    [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
    [T2Space G] [TotallyDisconnectedSpace G]
    [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [CompactSpace H]
    [T2Space H] [TotallyDisconnectedSpace H]
    (φ : ContinuousMonoidHom G H) (hφ : Function.Surjective φ) :
    proPKernel p H ≤ (proPKernel p G).map φ.toMonoidHom := by
  set Nim := (proPKernel p G).map φ.toMonoidHom with hNim
  haveI hNnorm : Nim.Normal := (proPKernel_normal p G).map φ.toMonoidHom hφ
  haveI hNclosed : IsClosed (Nim : Set H) := by
    rw [hNim, Subgroup.coe_map]
    exact ((proPKernel_isClosed p G).isCompact.image φ.continuous_toFun).isClosed
  -- the surjection `G ↠ H⧸Nim` kills `proPKernel p G`, so descends to `G(p) ↠ H⧸Nim`
  have hle : proPKernel p G ≤ ((quotientMk Nim).comp φ).toMonoidHom.ker := by
    intro g hg
    rw [MonoidHom.mem_ker]
    show quotientMk Nim (φ g) = 1
    rw [quotientMk_eq_one_iff, hNim]
    exact Subgroup.mem_map.mpr ⟨g, hg, rfl⟩
  have hτraw : Function.Surjective ((quotientMk Nim).comp φ) :=
    (quotientMk_surjective Nim).comp hφ
  have hτsurj : Function.Surjective (quotientLift (proPKernel p G) ((quotientMk Nim).comp φ) hle) := by
    intro y
    obtain ⟨x, hx⟩ := hτraw y
    exact ⟨quotientMk (proPKernel p G) x,
      (quotientLift_quotientMk (proPKernel p G) ((quotientMk Nim).comp φ) hle x).trans hx⟩
  have hHNproP : IsProP p (H ⧸ Nim) :=
    isProP_of_surjective (quotientLift (proPKernel p G) ((quotientMk Nim).comp φ) hle).toMonoidHom
      (quotientLift (proPKernel p G) ((quotientMk Nim).comp φ) hle).continuous_toFun hτsurj
      isProP_quotient_proPKernel
  have hpk : proPKernel p H ≤ (quotientMk Nim).toMonoidHom.ker :=
    proPKernel_le_ker hHNproP (quotientMk Nim)
  intro h hh
  have hmem : quotientMk Nim h = 1 := hpk hh
  exact (QuotientGroup.eq_one_iff h).mp hmem

/-- **`τ` dies in the maximal pro-2 quotient of `T_tame`** (Lemma 3.1): in every finite 2-group
level the image of `τ` has both odd order (tame relation `τ^σ = τ²`) and 2-power order. -/
theorem maxProPMk_tameTau : maxProPMk 2 Ttame tameTau = 1 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hmem : tameTau ∈ proPKernel 2 Ttame := by
    rw [proPKernel, Subgroup.mem_iInf]
    rintro ⟨U, hU⟩
    set q : Ttame →* Ttame ⧸ U.toSubgroup := QuotientGroup.mk' U.toSubgroup with hq
    have hrel : (q tameSigma)⁻¹ * (q tameTau) * (q tameSigma) = (q tameTau) ^ 2 := by
      have h := congrArg (⇑q) GQ2.tame_relation
      simpa only [conjP, map_mul, map_inv, map_pow] using h
    have hodd : Odd (orderOf (q tameTau)) :=
      Tame.tame_odd_order (orderOf_pos (q tameSigma)).ne' hrel
    obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.mp hU) (q tameTau)
    have h1 : orderOf (q tameTau) = 1 := by
      rcases Nat.eq_zero_or_pos k with rfl | hpos
      · simpa using hk
      · exfalso
        have h2dvd : 2 ∣ orderOf (q tameTau) := hk ▸ dvd_pow_self 2 hpos.ne'
        rw [Nat.odd_iff] at hodd; omega
    exact (QuotientGroup.eq_one_iff _).mp (orderOf_eq_one_iff.mp h1)
  exact (quotientMk_eq_one_iff (proPKernel 2 Ttame)).mpr hmem

/-- **`ker ν_t ⊆ proPKernel 2 T_tame`.**  `maxProPMk : T_tame ↠ T_tame(2)` factors through
`ν_t : T_tame ↠ ℤ₂` — build `ρ' : ℤ₂ → T_tame(2)` from the `ẑ`-power hom `ẑ ↦ (maxProPMk σ)^ẑ`
(pushed through `ℤ₂ = ẑ(2)` since `T_tame(2)` is pro-2), matching `maxProPMk` on `σ` (both `↦
maxProPMk σ`) and on `τ` (both `↦ 1`, via `maxProPMk_tameTau`).  Hence `ν_t x = 1 ⇒ maxProPMk x =
ρ'(ν_t x) = 1 ⇒ x ∈ proPKernel`. -/
theorem ker_nuT_le_proPKernel :
    GQ2.nuT.toMonoidHom.ker ≤ proPKernel 2 Ttame := by
  set s : maxProPQuotient 2 Ttame := maxProPMk 2 Ttame tameSigma with hs
  -- the `ẑ`-power hom `Zhat → T_tame(2)`, generator ↦ `s`
  let zhatHom : ContinuousMonoidHom Zhat (maxProPQuotient 2 Ttame) :=
    ⟨{ toFun := fun γ => s ^ᶻ γ, map_one' := zpowHat_one s, map_mul' := fun a b => zpowHat_mul s a b },
      continuous_zpowHat s⟩
  -- descend through `ℤ₂ = Zhat(2)` (the target is pro-2)
  let ρ' : ContinuousMonoidHom Ztwo (maxProPQuotient 2 Ttame) :=
    (maxProPHomEquiv (G := Zhat) isProP_maxProPQuotient).symm zhatHom
  have hρ : ∀ z : Zhat, ρ' (maxProPMk 2 Zhat z) = s ^ᶻ z := fun z => rfl
  -- `maxProPMk = ρ' ∘ ν_t` by density on `σ, τ`
  have key : ∀ y, (maxProPMk 2 Ttame) y = (ρ'.comp GQ2.nuT) y := by
    refine monoidHom_eq_of_topGen (f := (maxProPMk 2 Ttame).toMonoidHom)
      (g := (ρ'.comp GQ2.nuT).toMonoidHom)
      (maxProPMk 2 Ttame).continuous_toFun (ρ'.comp GQ2.nuT).continuous_toFun topGen_ttame ?_
    rintro z (rfl | rfl)
    · show maxProPMk 2 Ttame tameSigma = ρ' (GQ2.nuT tameSigma)
      rw [nuT_tameSigma, show ztwoOne = maxProPMk 2 Zhat (Zhat.ofInt 1) from rfl, hρ,
        zpowHat_ofInt, zpow_one]
    · show maxProPMk 2 Ttame tameTau = ρ' (GQ2.nuT tameTau)
      rw [nuT_tameTau, map_one, maxProPMk_tameTau]
  intro x hx
  have hnuT : GQ2.nuT x = 1 := hx
  have hmk : maxProPMk 2 Ttame x = 1 := by
    rw [key x]; show ρ' (GQ2.nuT x) = 1; rw [hnuT, map_one]
  exact (QuotientGroup.eq_one_iff x).mp hmk

/-! ## The `Γ_A` side -/

/-- `φ_A : Γ_A ↠ T_tame` is surjective (Prop 3.2, via `tameAEquiv`). -/
theorem phiA_surjective : Function.Surjective phiA := by
  intro t
  obtain ⟨x, hx⟩ := tameAEquiv.surjective t
  obtain ⟨g, rfl⟩ := quotientMk_surjective wildPartB x
  exact ⟨g, hx⟩

/-- `φ_Π : Γ_A ↠ Π` is surjective (P-25 `prop_3_10_gammaA`, via `maxAEquiv`). -/
theorem phiP_surjective : Function.Surjective phiP := by
  intro p
  obtain ⟨x, hx⟩ := maxAEquiv.surjective p
  obtain ⟨g, rfl⟩ := quotientMk_surjective (proPKernel 2 GammaA) x
  exact ⟨g, hx⟩

/-- `ν_t ∘ φ_A = ν₂ ∘ φ_Π` on `Γ_A`: density on the four marked generators. -/
theorem compatA_proved (g : GammaA) : GQ2.nuT (phiA g) = GQ2.nuTwo (phiP g) := by
  have key : ∀ x, (GQ2.nuT.comp phiA) x = (GQ2.nuTwo.comp phiP) x := by
    refine monoidHom_eq_of_topGen (f := (GQ2.nuT.comp phiA).toMonoidHom)
      (g := (GQ2.nuTwo.comp phiP).toMonoidHom)
      (GQ2.nuT.comp phiA).continuous_toFun (GQ2.nuTwo.comp phiP).continuous_toFun
      topGen_gammaA ?_
    rintro z (rfl | rfl | rfl | rfl)
    · show GQ2.nuT (phiA gammaSigma) = GQ2.nuTwo (phiP gammaSigma)
      rw [phiA_gammaSigma, phiP_gammaSigma, nuT_tameSigma, nuTwo_piSigma]
    · show GQ2.nuT (phiA gammaTau) = GQ2.nuTwo (phiP gammaTau)
      rw [phiA_gammaTau, phiP_gammaTau, nuT_tameTau, map_one]
    · show GQ2.nuT (phiA gammaX0) = GQ2.nuTwo (phiP gammaX0)
      rw [phiA_gammaX0, phiP_gammaX0, map_one, nuTwo_piX0]
    · show GQ2.nuT (phiA gammaX1) = GQ2.nuTwo (phiP gammaX1)
      rw [phiA_gammaX1, phiP_gammaX1, map_one, nuTwo_piX1]
  exact key g

/-! ## The `G_{ℚ₂}` side -/

variable [CompactSpace AbsGalQ2] [TotallyDisconnectedSpace AbsGalQ2]

/-- The chosen local tame quotient (B10 + Lemma 3.3), `prop_3_2_local`. -/
noncomputable def locTame : LocalTameQuotient := (prop_3_2_local).some

instance locTame_W_normal : locTame.W.Normal := locTame.normal

/-- The chosen local pro-2 marked iso (P-25 `prop_3_10_local_marked`) at `R = localReciprocity`. -/
noncomputable def locPro2 := prop_3_10_local_marked_proved (localReciprocity)

/-- `tameF : G_{ℚ₂} ↠ T_tame`, the tame quotient map (composite `G ↠ G/W ≅ T_tame`). -/
noncomputable def tameFHom : ContinuousMonoidHom AbsGalQ2 Ttame :=
  haveI := locTame.normal
  (⟨locTame.equiv.toMulEquiv.toMonoidHom, locTame.equiv.continuous_toFun⟩ :
    ContinuousMonoidHom (AbsGalQ2 ⧸ locTame.W) Ttame).comp (quotientMk locTame.W)

@[simp] lemma tameFHom_apply (x : AbsGalQ2) :
    tameFHom x = locTame.equiv (quotientMk locTame.W x) := rfl

/-- `pro2F : G_{ℚ₂} ↠ Π`, the maximal pro-2 quotient map (composite `G ↠ G(2) ≅ Π`). -/
noncomputable def pro2FHom : ContinuousMonoidHom AbsGalQ2 PiBd :=
  (⟨locPro2.choose_spec.2.choose.toMulEquiv.toMonoidHom,
      locPro2.choose_spec.2.choose.continuous_toFun⟩ :
    ContinuousMonoidHom (maxProPQuotient 2 AbsGalQ2) PiBd).comp (maxProPMk 2 AbsGalQ2)

@[simp] lemma pro2FHom_apply (x : AbsGalQ2) :
    pro2FHom x = locPro2.choose_spec.2.choose (maxProPMk 2 AbsGalQ2 x) := rfl

theorem tameFHom_surjective : Function.Surjective tameFHom := by
  haveI := locTame.normal
  exact locTame.equiv.surjective.comp (quotientMk_surjective locTame.W)

theorem pro2FHom_surjective : Function.Surjective pro2FHom :=
  locPro2.choose_spec.2.choose.surjective.comp (quotientMk_surjective (proPKernel 2 AbsGalQ2))

/-- `ker tameF = W`. -/
theorem ker_tameFHom : tameFHom.toMonoidHom.ker = locTame.W := by
  haveI := locTame.normal
  ext x
  rw [MonoidHom.mem_ker]
  constructor
  · intro h
    have hx1 : quotientMk locTame.W x = 1 :=
      locTame.equiv.injective (by rw [map_one]; exact h)
    exact (QuotientGroup.eq_one_iff x).mp hx1
  · intro h
    show locTame.equiv (quotientMk locTame.W x) = 1
    have hmk : quotientMk locTame.W x = 1 := (QuotientGroup.eq_one_iff x).mpr h
    rw [hmk, map_one]

/-- `ker pro2F = proPKernel 2 G_{ℚ₂}`. -/
theorem ker_pro2FHom : pro2FHom.toMonoidHom.ker = proPKernel 2 AbsGalQ2 := by
  ext x
  rw [MonoidHom.mem_ker]
  constructor
  · intro h
    have hx1 : maxProPMk 2 AbsGalQ2 x = 1 :=
      locPro2.choose_spec.2.choose.injective (by rw [map_one]; exact h)
    exact (QuotientGroup.eq_one_iff x).mp hx1
  · intro h
    show locPro2.choose_spec.2.choose (maxProPMk 2 AbsGalQ2 x) = 1
    have hmk : maxProPMk 2 AbsGalQ2 x = 1 := (QuotientGroup.eq_one_iff x).mpr h
    rw [hmk, map_one]

/-- **Tame reciprocity — the one arithmetic gap** (see module docstring).  `ι(ν_t(tameF g))`
equals `ν_ur(toAb g)`; equivalently, the tame quotient's unramified character is `ν_ur`. -/
theorem tame_reciprocity (g : AbsGalQ2) :
    locPro2.choose (GQ2.nuT (tameFHom g)) = (localReciprocity).nu_ur (toAb g) := by
  sorry

/-- `ν_t ∘ tameF = ν₂ ∘ pro2F` on `G_{ℚ₂}` — from `tame_reciprocity` and `prop_3_10_local_marked`. -/
theorem compatF_proved (g : AbsGalQ2) : GQ2.nuT (tameFHom g) = GQ2.nuTwo (pro2FHom g) := by
  have key : locPro2.choose (GQ2.nuT (tameFHom g))
      = locPro2.choose (GQ2.nuTwo (pro2FHom g)) := by
    rw [tame_reciprocity g]
    exact locPro2.choose_spec.2.choose_spec g
  exact locPro2.choose.injective key

/-! ## Assembling the boundary maps -/

/-- The kernel hypothesis for `fiberProductExists`, uniformly: `pro2X` maps `ker tameX` onto
`ker ν₂`, via `ker ν_t ⊆ proPKernel 2 T_tame ⊆ tameX(proPKernel 2 dom) ⊆ tameX(ker tameX)`
(the last since `proPKernel 2 dom ≤ ker pro2X` and we correct within `ker pro2X`). -/
theorem hker_uniform {dom : Type*} [Group dom] [TopologicalSpace dom] [IsTopologicalGroup dom]
    [CompactSpace dom] [T2Space dom] [TotallyDisconnectedSpace dom]
    (tameX : ContinuousMonoidHom dom Ttame) (pro2X : ContinuousMonoidHom dom PiBd)
    (htame : Function.Surjective tameX) (hpro : Function.Surjective pro2X)
    (hkerpro : proPKernel 2 dom ≤ pro2X.toMonoidHom.ker)
    (hcompat : ∀ g, GQ2.nuT (tameX g) = GQ2.nuTwo (pro2X g))
    (b : PiBd) (hb : GQ2.nuTwo b = 1) :
    ∃ g : dom, tameX g = 1 ∧ pro2X g = b := by
  obtain ⟨g₀, hg₀⟩ := hpro b
  have htk : GQ2.nuT (tameX g₀) = 1 := by rw [hcompat g₀, hg₀]; exact hb
  have htg0 : tameX g₀ ∈ proPKernel 2 Ttame := ker_nuT_le_proPKernel htk
  have hmem : tameX g₀ ∈ (proPKernel 2 dom).map tameX.toMonoidHom :=
    proPKernel_image_ge tameX htame htg0
  obtain ⟨k, hk, hkval⟩ := Subgroup.mem_map.mp hmem
  have hkval' : tameX k = tameX g₀ := hkval
  refine ⟨g₀ * k⁻¹, ?_, ?_⟩
  · show tameX (g₀ * k⁻¹) = 1
    rw [map_mul, map_inv, hkval', mul_inv_cancel]
  · have hkpro : pro2X k = 1 := by
      have : k ∈ pro2X.toMonoidHom.ker := hkerpro hk
      rwa [MonoidHom.mem_ker] at this
    show pro2X (g₀ * k⁻¹) = b
    rw [map_mul, map_inv, hkpro, inv_one, mul_one, hg₀]

/-- **`prop_3_14` witness**: the full `BoundaryMaps` bundle. -/
noncomputable def boundaryMapsWitness : BoundaryMaps where
  tameA := phiA
  pro2A := phiP
  compatA := compatA_proved
  tameA_sigma := phiA_gammaSigma
  tameA_tau := phiA_gammaTau
  tameA_x0 := phiA_gammaX0
  tameA_x1 := phiA_gammaX1
  pro2A_sigma := phiP_gammaSigma
  pro2A_tau := phiP_gammaTau
  pro2A_x0 := phiP_gammaX0
  pro2A_x1 := phiP_gammaX1
  surjA := by
    rintro ⟨⟨t, p⟩, hmem⟩
    obtain ⟨g, hg1, hg2⟩ := fiberProductExists GQ2.nuT.toMonoidHom GQ2.nuTwo.toMonoidHom
      phiA.toMonoidHom phiP.toMonoidHom phiA_surjective compatA_proved
      (hker_uniform phiA phiP phiA_surjective phiP_surjective
        (proPKernel_le_ker piBd_isProP phiP) compatA_proved) t p hmem
    exact ⟨g, Subtype.ext (Prod.ext hg1 hg2)⟩
  tameF := tameFHom
  pro2F := pro2FHom
  compatF := compatF_proved
  tameF_surjective := tameFHom_surjective
  wild_isProP := by rw [ker_tameFHom]; exact locTame.isProP
  wild_isMax := by
    intro N hNn hNc hNp
    rw [ker_tameFHom]; exact locTame.maximal N hNn hNc hNp
  pro2F_surjective := pro2FHom_surjective
  ker_pro2F := ker_pro2FHom
  surjF := by
    rintro ⟨⟨t, p⟩, hmem⟩
    obtain ⟨g, hg1, hg2⟩ := fiberProductExists GQ2.nuT.toMonoidHom GQ2.nuTwo.toMonoidHom
      tameFHom.toMonoidHom pro2FHom.toMonoidHom tameFHom_surjective compatF_proved
      (hker_uniform tameFHom pro2FHom tameFHom_surjective pro2FHom_surjective
        ker_pro2FHom.ge compatF_proved) t p hmem
    exact ⟨g, Subtype.ext (Prod.ext hg1 hg2)⟩

/-- **Prop. 3.14** (proved modulo `tame_reciprocity`): the eq. (27) boundary data exists. -/
theorem prop_3_14_proved : Nonempty BoundaryMaps :=
  ⟨boundaryMapsWitness⟩

end SectionThree

end GQ2
