import GQ2.BoundaryConstruction
import GQ2.LocalMarked
import GQ2.Prop32
import GQ2.TameTwoQuotient

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

/-! ## Reciprocity-side reduction kit (P-25b): `tame_reciprocity ⟸` two atomic values

Both `f₁ = ι∘ν_t∘tameF` and `ν_ur∘toAb` factor through `G_{ℚ₂}^{ab}` (abelian target `ℤ₂`); by
`denseRange_recip` they agree iff they agree on `recip(ℚ₂ˣ)`.  Two continuous homs `ℚ₂ˣ → ℤ₂`
agreeing on the square-class generators `{−4, 2, −3}` (`units_gen`) are equal — their quotient's
range is infinitely 2-divisible in `ℤ₂`, hence `0`.  The `−4`-value is automatic (`−4 = (−1)·2²`,
`−1` is 2-torsion into torsion-free `ℤ₂`), so only `μ(2)` and `μ(−3)` remain as atoms. -/

/-- `x² = 1` in `Multiplicative ℤ₂` forces `x = 1` (`ℤ₂` torsion-free). -/
lemma mult_padic_sq_eq_one {x : Multiplicative ℤ_[2]} (hx : x ^ 2 = 1) : x = 1 := by
  have h : Multiplicative.toAdd x + Multiplicative.toAdd x = 0 := by
    have h0 := congrArg Multiplicative.toAdd hx
    rw [pow_two] at h0; exact h0
  have ha : Multiplicative.toAdd x = 0 := by
    have h2 : (2 : ℤ_[2]) * Multiplicative.toAdd x = 0 := by rw [two_mul]; exact h
    rcases mul_eq_zero.mp h2 with hc | ha
    · exact absurd hc (by norm_num)
    · exact ha
  exact Multiplicative.toAdd.injective (by rw [ha]; rfl)

/-- An element of `ℤ_[2]` divisible by `2^n` for every `n` is `0`. -/
lemma padicInt_eq_zero_of_forall_two_pow_dvd {z : ℤ_[2]}
    (h : ∀ n : ℕ, (2:ℤ_[2])^n ∣ z) : z = 0 := by
  rw [← norm_eq_zero]
  by_contra hne
  have hpos : 0 < ‖z‖ := (norm_nonneg z).lt_of_ne (Ne.symm hne)
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hpos (show (2:ℝ)⁻¹ < 1 by norm_num)
  obtain ⟨w, hw⟩ := h n
  have h2 : ‖(2:ℤ_[2])‖ = (2:ℝ)⁻¹ := by
    have hc : (2:ℤ_[2]) = ((2:ℕ):ℤ_[2]) := by norm_cast
    rw [hc, PadicInt.norm_p]; norm_num
  have hle : ‖z‖ ≤ (2:ℝ)⁻¹ ^ n :=
    calc ‖z‖ = ‖(2:ℤ_[2])^n * w‖ := by rw [hw]
      _ = ‖(2:ℤ_[2])‖^n * ‖w‖ := by rw [norm_mul, norm_pow]
      _ ≤ ‖(2:ℤ_[2])‖^n * 1 := by gcongr; exact PadicInt.norm_le_one w
      _ = (2:ℝ)⁻¹ ^ n := by rw [h2, mul_one]
  exact absurd (lt_of_le_of_lt hle hn) (lt_irrefl _)

/-- **Square-class rigidity of `ℤ₂`-characters of `ℚ₂ˣ`.**  Two continuous homs `ℚ₂ˣ → ℤ₂`
agreeing on `{2, −3}` are equal: the `−4`-value is automatic, and `units_gen` + infinite
2-divisibility force the rest. -/
lemma padic_hom_eq_of_gens (φ ψ : ℚ_[2]ˣ →* Multiplicative ℤ_[2])
    (h2 : φ uniformizer = ψ uniformizer) (h3 : φ unitNeg3 = ψ unitNeg3) (x : ℚ_[2]ˣ) :
    φ x = ψ x := by
  set δ : ℚ_[2]ˣ →* Multiplicative ℤ_[2] := φ / ψ with hδdef
  have hδ2 : δ uniformizer = 1 := by rw [hδdef, MonoidHom.div_apply, h2, div_self']
  have hδ3 : δ unitNeg3 = 1 := by rw [hδdef, MonoidHom.div_apply, h3, div_self']
  -- `−4 = (−1)·2²`; `−1` is 2-torsion, so `δ(−4) = 1` automatically
  have hdecomp : unitNeg4 = unitEmbed (-1) * uniformizer ^ 2 := by
    apply Units.ext
    push_cast [unitNeg4, uniformizer, unitEmbed_val]
    norm_num
  have hδneg1 : δ (unitEmbed (-1)) = 1 := by
    apply mult_padic_sq_eq_one
    rw [← map_pow, show (unitEmbed (-1 : ℤ_[2]ˣ)) ^ 2 = 1 by rw [← map_pow]; norm_num, map_one]
  have hδ4 : δ unitNeg4 = 1 := by
    rw [hdecomp, map_mul, map_pow, hδneg1, hδ2, one_pow, one_mul]
  -- `δ` kills the square-class generators, so `δ x` is infinitely 2-divisible
  have hker : ∀ y ∈ ({unitNeg4, uniformizer, unitNeg3} : Set ℚ_[2]ˣ), δ y = 1 := by
    rintro y (rfl | rfl | rfl)
    exacts [hδ4, hδ2, hδ3]
  have hstep : ∀ z : ℚ_[2]ˣ, ∃ t,
      Multiplicative.toAdd (δ z) = 2 * Multiplicative.toAdd (δ t) := by
    intro z
    obtain ⟨s, hs, t, hz⟩ := units_gen z
    refine ⟨t, ?_⟩
    have hds : δ s = 1 :=
      (Subgroup.closure_le δ.ker).mpr (fun y hy => MonoidHom.mem_ker.mpr (hker y hy)) hs
    rw [hz, map_mul, hds, one_mul, map_pow, pow_two, two_mul]; rfl
  have hdvd : ∀ n : ℕ, ∀ z, (2:ℤ_[2])^n ∣ Multiplicative.toAdd (δ z) := by
    intro n
    induction n with
    | zero => intro z; simp
    | succ k ih =>
        intro z
        obtain ⟨t, ht⟩ := hstep z
        obtain ⟨w, hw⟩ := ih t
        exact ⟨w, by rw [ht, hw]; ring⟩
  have hzero : Multiplicative.toAdd (δ x) = 0 :=
    padicInt_eq_zero_of_forall_two_pow_dvd (fun n => hdvd n x)
  have hδ1 : δ x = 1 := Multiplicative.toAdd.injective (by rw [hzero]; rfl)
  rw [hδdef, MonoidHom.div_apply] at hδ1
  exact div_eq_one.mp hδ1

/-! ## The `G_{ℚ₂}` side -/

variable [CompactSpace AbsGalQ2] [TotallyDisconnectedSpace AbsGalQ2]

/-- The chosen local tame quotient: **the B10′ oriented witness** (`GQ2.tameQuotient`), with
Lemma 3.3's maximality attached (`tameData_maximal`).  Using the axiom's witness directly (not
`prop_3_2_local.some`) keeps the orientation clauses `nuT_recip_unit`/`nuT_recip_uniformizer`
available for the two `tame_recip_*` atoms below. -/
noncomputable def locTame : LocalTameQuotient :=
  { toTameQuotientData := GQ2.tameQuotient.toTameQuotientData,
    maximal := tameData_maximal GQ2.tameQuotient.toTameQuotientData }


/-- The chosen local pro-2 marked iso (P-25 `prop_3_10_local_marked`) at `R = localReciprocity`. -/
noncomputable def locPro2 := prop_3_10_local_marked_proved (localReciprocity)

/-- `tameF : G_{ℚ₂} ↠ T_tame`, the tame quotient map (composite `G ↠ G/W ≅ T_tame`). -/
noncomputable def tameFHom : ContinuousMonoidHom AbsGalQ2 Ttame :=
  haveI := locTame.normal
  (⟨locTame.equiv.toMulEquiv.toMonoidHom, locTame.equiv.continuous_toFun⟩ :
    ContinuousMonoidHom (AbsGalQ2 ⧸ locTame.W) Ttame).comp (quotientMk locTame.W)


/-- `pro2F : G_{ℚ₂} ↠ Π`, the maximal pro-2 quotient map (composite `G ↠ G(2) ≅ Π`). -/
noncomputable def pro2FHom : ContinuousMonoidHom AbsGalQ2 PiBd :=
  (⟨locPro2.choose_spec.2.choose.toMulEquiv.toMonoidHom,
      locPro2.choose_spec.2.choose.continuous_toFun⟩ :
    ContinuousMonoidHom (maxProPQuotient 2 AbsGalQ2) PiBd).comp (maxProPMk 2 AbsGalQ2)


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

/-- The tame unramified character `f₁ = ι∘ν_t∘tameF : G_{ℚ₂} → Multiplicative ℤ₂`. -/
noncomputable def tameCharRaw : ContinuousMonoidHom AbsGalQ2 (Multiplicative ℤ_[2]) :=
  (⟨locPro2.choose.toMulEquiv.toMonoidHom, locPro2.choose.continuous_toFun⟩ :
    ContinuousMonoidHom Ztwo (Multiplicative ℤ_[2])).comp (GQ2.nuT.comp tameFHom)

/-- `f₁` descended through the topological abelianization `G_{ℚ₂}^{ab}`. -/
noncomputable def tameChar : ContinuousMonoidHom AbsGalQ2ab (Multiplicative ℤ_[2]) :=
  abLiftG tameCharRaw

@[simp] lemma tameChar_toAb (g : AbsGalQ2) :
    tameChar (toAb g) = locPro2.choose (GQ2.nuT (tameFHom g)) :=
  abLiftG_abMk tameCharRaw g

/-- **Atom (F)** — the uniformizer: `f₁(rec 2) = ofAdd(−1)` (arithmetic Frobenius, geometric
coordinate `−1`).  Discharged by the B10′ orientation clause `nuT_recip_uniformizer`. -/
theorem tame_recip_uniformizer :
    tameChar ((localReciprocity).recip uniformizer)
      = Multiplicative.ofAdd ((-1 : ℤ) : ℤ_[2]) := by
  obtain ⟨g, hg⟩ :=
    QuotientGroup.mk'_surjective commClosure ((localReciprocity).recip uniformizer)
  have hg' : toAb g = (localReciprocity).recip uniformizer := hg
  have hval : GQ2.nuT (tameFHom g) = ztwoOne⁻¹ :=
    GQ2.tameQuotient.nuT_recip_uniformizer g hg'
  rw [← hg', tameChar_toAb, hval, map_inv, locPro2.choose_spec.1, ← ofAdd_neg]
  congr 1

/-- **Atom (U₋₃)** — the unit `−3`: `f₁(rec(−3)) = 1` (unramified-trivial).  Discharged by the
B10′ orientation clause `nuT_recip_unit` at the unit `−3` (odd, hence a `ℤ₂`-unit). -/
theorem tame_recip_unitNeg3 :
    tameChar ((localReciprocity).recip unitNeg3) = 1 := by
  obtain ⟨u, hu⟩ : ∃ u : ℤ_[2]ˣ, (u : ℤ_[2]) = -3 :=
    ⟨(isUnit_intCast_of_odd (⟨-2, by ring⟩ : Odd (-3 : ℤ))).unit, by
      rw [IsUnit.unit_spec]
      push_cast
      ring⟩
  have hemb : unitEmbed u = unitNeg3 := by
    apply Units.ext
    rw [unitEmbed_val, hu]
    show algebraMap ℤ_[2] ℚ_[2] (-3) = ((unitNeg3 : ℚ_[2]ˣ) : ℚ_[2])
    simp only [unitNeg3, Units.val_mk0, map_neg, map_ofNat]
  obtain ⟨g, hg⟩ :=
    QuotientGroup.mk'_surjective commClosure ((localReciprocity).recip unitNeg3)
  have hg' : toAb g = (localReciprocity).recip unitNeg3 := hg
  have hval : GQ2.nuT (tameFHom g) = 1 :=
    GQ2.tameQuotient.nuT_recip_unit u g (by rw [hg', hemb])
  rw [← hg', tameChar_toAb, hval, map_one]

/-- **Tame reciprocity** (P-25b reduction): `ι(ν_t(tameF g)) = ν_ur(toAb g)`.  Both sides factor
through `G_{ℚ₂}^{ab}`; agree on the dense image of `recip` by `padic_hom_eq_of_gens`, whose two
generator inputs are exactly the atoms `tame_recip_uniformizer` (F) and `tame_recip_unitNeg3`
(U₋₃) matched against `nu_ur_recip_*`. -/
theorem tame_reciprocity (g : AbsGalQ2) :
    locPro2.choose (GQ2.nuT (tameFHom g)) = (localReciprocity).nu_ur (toAb g) := by
  have key : ⇑tameChar = ⇑(localReciprocity).nu_ur := by
    apply Continuous.ext_on (localReciprocity).denseRange_recip tameChar.continuous_toFun
      (localReciprocity).continuous_nu_ur
    rintro _ ⟨u, rfl⟩
    refine padic_hom_eq_of_gens (tameChar.toMonoidHom.comp (localReciprocity).recip)
      ((localReciprocity).nu_ur.comp (localReciprocity).recip) ?_ ?_ u
    · show tameChar ((localReciprocity).recip uniformizer)
        = (localReciprocity).nu_ur ((localReciprocity).recip uniformizer)
      rw [tame_recip_uniformizer, nu_ur_recip_uniformizer']
    · show tameChar ((localReciprocity).recip unitNeg3)
        = (localReciprocity).nu_ur ((localReciprocity).recip unitNeg3)
      rw [tame_recip_unitNeg3, nu_ur_recip_unitNeg3, Int.cast_zero, ofAdd_zero]
  have h := congrFun key (toAb g)
  rw [tameChar_toAb] at h
  exact h

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

/-! ### Paper-tag ledger (auto-generated by paperforge; do not edit)

  * eq. (27) = ⟦eq-boundarymap⟧
  * Lemma 3.3 = ⟦lem-o2tame⟧
  * Prop 3.14 = ⟦prop-compatiblemarking⟧
  * Prop 3.2 = ⟦prop-tamequotient⟧
-/
