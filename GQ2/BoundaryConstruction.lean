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

## STATUS (P-25, 2026-07-04)

* **`prop_3_10_gammaA` — DONE** (`prop_3_10_gammaA_proved`, std-3; spliced into
  `SectionThreeMarked.lean`).  Full marked iso `Γ_A(2) ≅ Π` via the forward descent `phiP`
  (= `PhiMax`) and the backward `PsiMax`, glued by density (`PhiMax_PsiMax`/`PsiMax_PhiMax`).
* **`phiP : Γ_A → Π` — DONE**; this is exactly Prop 3.14's `pro2A` field (with the four
  `phiP_gamma*` generator values), ready for the `prop_3_14` bundle.
* **`prop_3_14 : Nonempty BoundaryMaps` — REMAINING.**  The `BoundaryMaps` bundle
  (`GQ2/BoundaryFrame.lean`) has 20 fields spanning **both** sides.  Γ_A side: `tameA` = P-09's
  `phiA`, `pro2A` = `phiP` (done here), `compatA` (`nuT∘tameA = nuTwo∘pro2A` — a density check on
  generators through `nuT_tame*`/`nuTwo_pi*`), `surjA`.  G_ℚ₂ side: `tameF`/`wild_isProP`/
  `wild_isMax` from P-09's `prop_3_2_local` (`LocalTameQuotient`), `pro2F`/`ker_pro2F`/
  `pro2F_surjective` = the max pro-`2` quotient map of `AbsGalQ2`, `compatF`, `surjF` — the last
  three gated on `prop_3_10_local_marked`.
* **`prop_3_10_local_marked : (Π,ν₂) ≅ (G_ℚ₂(2),ν_ur)` — REMAINING.**  The anabelian core:
  `prop_1_1` (P-10, `PropOneOneAssembly.lean`: `G_ℚ₂(2) ≅ ⟨a,s,y | a²s⁴[s,y]⟩`, `ν_ur=(−2,1,0)`)
  identified with `Π`'s presentation, plus the `Ztwo ≅ Multiplicative ℤ₂` seam
  `ztwoEquivPadic` (P-21, `ZtwoPowering.lean`) for the two `ν`-targets, and the Nielsen change
  of generators (Cor 3.12).
-/

namespace GQ2

namespace SectionThree

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
  have hu0 : t.u0 = x₀ := by rw [show t.u0 = powOmega2 (x₀ * 1) from rfl, mul_one, hx0]
  have hu1 : t.u1 = x₁ := by rw [show t.u1 = powOmega2 (x₁ * 1) from rfl, mul_one, hx1]
  have hs2 : t.sigma2 = σ := hσ
  have hd0 : t.d0 = 1 := by rw [Marking.d0, hu0, show t.x₀ = x₀ from rfl, mul_inv_cancel]
  have hc0 : t.c0 = 1 := by rw [Marking.c0, hd0]; simp [commP]
  have hg0 : t.g0 = σ ^ 2 := by rw [Marking.g0, hs2]
  have hdg : t.dg = 1 := by rw [Marking.dg, hd0]; simp [conjP]
  have hhc : t.hc = 1 := by rw [Marking.hc, hdg, hd0]; simp [commP]
  have hh0 : t.h0 = conjP x₀ (σ ^ 2) * x₀ := by
    rw [Marking.h0, hdg, hd0, hhc, hg0, show t.x₀ = x₀ from rfl]; simp
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

/-! ## Topological generation of `Π` and the relator word -/

/-- The evaluation `F₃ → Π`, `σ ↦ πσ, x₀ ↦ πx₀, x₁ ↦ πx₁` (presentation projection then max
pro-`2` projection). -/
noncomputable def evalPi : ContinuousMonoidHom (FreeProfiniteGroup (Fin 3)) PiBd :=
  (maxProPMk 2 (profinitePresentation {piRelator})).comp
    (quotientMk (relatorSubgroup {piRelator}))

@[simp] lemma evalPi_of0 : evalPi (FreeProfiniteGroup.of 0) = piSigma := rfl
@[simp] lemma evalPi_of1 : evalPi (FreeProfiniteGroup.of 1) = piX0 := rfl
@[simp] lemma evalPi_of2 : evalPi (FreeProfiniteGroup.of 2) = piX1 := rfl

theorem evalPi_surjective : Function.Surjective evalPi :=
  (quotientMk_surjective _).comp (quotientMk_surjective _)

/-- `Π` is topologically generated by `πσ, πx₀, πx₁`. -/
theorem topGen_piBd :
    (Subgroup.closure {piSigma, piX0, piX1}).topologicalClosure = ⊤ := by
  have h := topGen_map (f := evalPi.toMonoidHom) evalPi.continuous_toFun evalPi_surjective
    (topGen_freeProfiniteGroup (Fin 3))
  have h1 : (⇑evalPi.toMonoidHom) '' Set.range (FreeProfiniteGroup.of (X := Fin 3))
      = {piSigma, piX0, piX1} := by
    rw [← Set.range_comp]
    ext z
    constructor
    · rintro ⟨i, rfl⟩; fin_cases i <;> simp
    · rintro (rfl | rfl | rfl)
      exacts [⟨0, rfl⟩, ⟨1, rfl⟩, ⟨2, rfl⟩]
  rwa [h1] at h

/-- In every discrete continuous quotient of `Π`, the images of `πσ, πx₀, πx₁` generate. -/
theorem gen_piBd_quotient {H : Type*} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [DiscreteTopology H] (f : PiBd →* H) (hcont : Continuous f) (hsurj : Function.Surjective f) :
    Subgroup.closure {f piSigma, f piX0, f piX1} = ⊤ := by
  have h := topGen_map f hcont hsurj topGen_piBd
  rw [Set.image_insert_eq, Set.image_insert_eq, Set.image_singleton] at h
  exact gen_of_topGen_discrete h

/-- The pro-`2` relator word (20) vanishes at `(πσ, πx₀, πx₁)`. -/
theorem piRelatorWord_eq_one :
    conjP piX0 (piSigma ^ 2) * piX0 * commP piX1 piSigma = 1 := by
  have hrel : evalPi piRelator = 1 := by
    show maxProPMk 2 (profinitePresentation {piRelator})
      (quotientMk (relatorSubgroup {piRelator}) piRelator) = 1
    rw [relator_quotientMk_eq_one {piRelator} (Set.mem_singleton _)]
    exact map_one _
  have hword : evalPi piRelator = conjP piX0 (piSigma ^ 2) * piX0 * commP piX1 piSigma := by
    simp only [piRelator, conjP, commP, map_mul, map_inv, map_pow, evalPi_of0, evalPi_of1,
      evalPi_of2]
  rw [← hword, hrel]

/-! ## The forward descent `Γ_A → Π` -/

/-- The pro-`2` classifier `F₄ ⟶ Π`: `σ ↦ πσ, τ ↦ 1, x₀ ↦ πx₀, x₁ ↦ πx₁`. -/
noncomputable def piClassifier : FreeProfiniteGroup (Fin 4) ⟶ PiBd :=
  (FreeProfiniteGroup.homEquiv (Fin 4) PiBd).symm ![piSigma, 1, piX0, piX1]

@[simp] lemma piClassifier_sigma : piClassifier.hom.toMonoidHom univMarking.σ = piSigma :=
  FreeProfiniteGroup.homEquiv_symm_of _ _ _
@[simp] lemma piClassifier_tau : piClassifier.hom.toMonoidHom univMarking.τ = 1 :=
  FreeProfiniteGroup.homEquiv_symm_of _ _ _
@[simp] lemma piClassifier_x0 : piClassifier.hom.toMonoidHom univMarking.x₀ = piX0 :=
  FreeProfiniteGroup.homEquiv_symm_of _ _ _
@[simp] lemma piClassifier_x1 : piClassifier.hom.toMonoidHom univMarking.x₁ = piX1 :=
  FreeProfiniteGroup.homEquiv_symm_of _ _ _

/-- Through every finite `2`-group level of `Π`, the marking pushed from the pro-`2` classifier is
admissible: `τ ↦ 1`, and the wild relator collapses to `piRelator`, which vanishes. -/
theorem isAdmissible_piClassifier_level (V : OpenNormalSubgroup PiBd) :
    (univMarking.map ((QuotientGroup.mk' V.toSubgroup).comp
      piClassifier.hom.toMonoidHom)).Admissible := by
  haveI : Finite (PiBd ⧸ V.toSubgroup) := inferInstance
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h2grp : IsPGroup 2 (PiBd ⧸ V.toSubgroup) := piBd_isProP V
  have ho : ∀ x : PiBd ⧸ V.toSubgroup, powOmega2 x = x := fun x => by
    obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.mp h2grp) x
    exact powOmega2_eq_self_of_orderOf_two_pow hk
  set q : PiBd →* PiBd ⧸ V.toSubgroup := QuotientGroup.mk' V.toSubgroup with hq
  set f : FreeProfiniteGroup (Fin 4) →* PiBd ⧸ V.toSubgroup :=
    q.comp piClassifier.hom.toMonoidHom with hf
  have hσ : (univMarking.map f).σ = q piSigma := congrArg q piClassifier_sigma
  have hτ : (univMarking.map f).τ = 1 := (congrArg q piClassifier_tau).trans (map_one q)
  have hx0 : (univMarking.map f).x₀ = q piX0 := congrArg q piClassifier_x0
  have hx1 : (univMarking.map f).x₁ = q piX1 := congrArg q piClassifier_x1
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- Generates
    rw [Marking.Generates, hσ, hτ, hx0, hx1]
    have hgen : Subgroup.closure {q piSigma, q piX0, q piX1} = ⊤ :=
      gen_piBd_quotient q continuous_quot_mk (QuotientGroup.mk'_surjective _)
    rw [eq_top_iff, ← hgen]
    refine Subgroup.closure_mono fun z hz => ?_
    rcases hz with rfl | rfl | rfl <;> simp
  · -- TameRel (τ = 1)
    rw [Marking.TameRel, hσ, hτ]
    simp [conjP]
  · -- WildRel via the collapse
    have ht : univMarking.map f = Marking.mk (q piSigma) 1 (q piX0) (q piX1) := by
      rw [show univMarking.map f = Marking.mk (univMarking.map f).σ (univMarking.map f).τ
        (univMarking.map f).x₀ (univMarking.map f).x₁ from rfl, hσ, hτ, hx0, hx1]
    rw [ht, wildRel_iff_piRelatorWord (q piSigma) (q piX0) (q piX1) (ho _) (ho _) (ho _)]
    have hpull : conjP (q piX0) ((q piSigma) ^ 2) * q piX0 * commP (q piX1) (q piSigma)
        = q (conjP piX0 (piSigma ^ 2) * piX0 * commP piX1 piSigma) := by
      simp only [map_mul, Marking.map_conjP, Marking.map_commP, map_pow]
    rw [hpull, piRelatorWord_eq_one, map_one]
  · -- Pro2Core: subgroups of the finite 2-group are 2-groups
    rw [Marking.Pro2Core, hx0, hx1]
    refine IsPGroup.iff_orderOf.mpr fun g => ?_
    obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.mp h2grp) (g : PiBd ⧸ V.toSubgroup)
    exact ⟨k, (Subgroup.orderOf_coe g).symm.trans hk⟩

/-- `N_A` is contained in the kernel of the pro-`2` classifier (each finite level is admissible). -/
theorem NA_le_ker_piClassifier : NA ≤ piClassifier.hom.toMonoidHom.ker := by
  intro x hx
  rw [MonoidHom.mem_ker]
  refine eq_one_of_forall_mem_openNormalSubgroup fun V => ?_
  haveI : Finite (PiBd ⧸ V.toSubgroup) := inferInstance
  set f : ContinuousMonoidHom (FreeProfiniteGroup (Fin 4)) (PiBd ⧸ V.toSubgroup) :=
    (quotientMk V.toSubgroup).comp piClassifier.hom with hf
  have hadm : (univMarking.map f.toMonoidHom).Admissible := isAdmissible_piClassifier_level V
  exact (QuotientGroup.eq_one_iff _).mp (MonoidHom.mem_ker.mp (NA_le_ker f hadm hx))

/-- The descent `φ_Π : Γ_A → Π` (`σ ↦ πσ, τ ↦ 1, x₀ ↦ πx₀, x₁ ↦ πx₁`) — Prop 3.14's `pro2A`. -/
noncomputable def phiP : ContinuousMonoidHom GammaA PiBd :=
  haveI : IsClosed (NA : Set (FreeProfiniteGroup (Fin 4))) := NA_isClosed
  quotientLift NA piClassifier.hom NA_le_ker_piClassifier

@[simp] lemma phiP_gammaSigma : phiP gammaSigma = piSigma := by
  haveI : IsClosed (NA : Set (FreeProfiniteGroup (Fin 4))) := NA_isClosed
  show phiP (quotientMk NA univMarking.σ) = piSigma
  exact (quotientLift_quotientMk _ _ _ _).trans piClassifier_sigma

@[simp] lemma phiP_gammaTau : phiP gammaTau = 1 := by
  haveI : IsClosed (NA : Set (FreeProfiniteGroup (Fin 4))) := NA_isClosed
  show phiP (quotientMk NA univMarking.τ) = 1
  exact (quotientLift_quotientMk _ _ _ _).trans piClassifier_tau

@[simp] lemma phiP_gammaX0 : phiP gammaX0 = piX0 := by
  haveI : IsClosed (NA : Set (FreeProfiniteGroup (Fin 4))) := NA_isClosed
  show phiP (quotientMk NA univMarking.x₀) = piX0
  exact (quotientLift_quotientMk _ _ _ _).trans piClassifier_x0

@[simp] lemma phiP_gammaX1 : phiP gammaX1 = piX1 := by
  haveI : IsClosed (NA : Set (FreeProfiniteGroup (Fin 4))) := NA_isClosed
  show phiP (quotientMk NA univMarking.x₁) = piX1
  exact (quotientLift_quotientMk _ _ _ _).trans piClassifier_x1

/-! ## The backward descent `Π → Γ_A(2)` -/

/-- The marked tame relation holds in `Γ_A` (relation (5) dies in the admissible limit). -/
theorem gammaMarking_tameRel : conjP gammaTau gammaSigma = gammaTau ^ 2 := by
  have h : quotientMk NA univMarking.tameRelator = 1 :=
    (quotientMk_eq_one_iff NA).mpr tameRelator_mem_NA
  have e : quotientMk NA univMarking.tameRelator
      = conjP gammaTau gammaSigma * (gammaTau ^ 2)⁻¹ := by
    rw [Marking.tameRelator]
    simp only [map_mul, map_inv, map_pow]
    rfl
  exact mul_inv_eq_one.mp (e.symm.trans h)

/-- **`τ` dies in the maximal pro-`2` quotient of `Γ_A`** (Lemma 3.1): in every finite `2`-group
level the image of `τ` has both odd order (tame relation) and `2`-power order, hence is trivial. -/
theorem maxProPMk_gammaTau : maxProPMk 2 GammaA gammaTau = 1 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hmem : gammaTau ∈ proPKernel 2 GammaA := by
    rw [proPKernel, Subgroup.mem_iInf]
    rintro ⟨U, hU⟩
    haveI : Finite (GammaA ⧸ U.toSubgroup) := inferInstance
    set q : GammaA →* GammaA ⧸ U.toSubgroup := QuotientGroup.mk' U.toSubgroup with hq
    have hrel : conjP (q gammaTau) (q gammaSigma) = (q gammaTau) ^ 2 := by
      have h := congrArg (⇑q) gammaMarking_tameRel
      rwa [Marking.map_conjP, map_pow] at h
    have hodd : Odd (orderOf (q gammaTau)) :=
      Tame.tame_odd_order (orderOf_pos (q gammaSigma)).ne' hrel
    obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.mp hU) (q gammaTau)
    have h1 : orderOf (q gammaTau) = 1 := by
      rcases Nat.eq_zero_or_pos k with rfl | hpos
      · simpa using hk
      · exfalso
        have h2dvd : 2 ∣ orderOf (q gammaTau) := hk ▸ dvd_pow_self 2 hpos.ne'
        rw [Nat.odd_iff] at hodd
        omega
    exact (QuotientGroup.eq_one_iff _).mp (orderOf_eq_one_iff.mp h1)
  exact (quotientMk_eq_one_iff (proPKernel 2 GammaA)).mpr hmem

/-- **The pro-`2` relator (20) holds in the maximal pro-`2` quotient of `Γ_A`.**  In every finite
`2`-group level the wild relation (6) holds (it dies in `Γ_A`, `wildRelator_mem_NA`) and `τ ↦ 1`,
so the collapse gives `piRelator = 1`; separated by finite quotients, it vanishes in the limit. -/
theorem piRelatorWord_maxA_eq_one :
    conjP (maxProPMk 2 GammaA gammaX0) ((maxProPMk 2 GammaA gammaSigma) ^ 2)
        * maxProPMk 2 GammaA gammaX0
        * commP (maxProPMk 2 GammaA gammaX1) (maxProPMk 2 GammaA gammaSigma) = 1 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set mk := maxProPMk 2 GammaA with hmkdef
  refine eq_one_of_forall_mem_openNormalSubgroup fun V => ?_
  haveI : Finite (maxProPQuotient 2 GammaA ⧸ V.toSubgroup) := inferInstance
  set q : ContinuousMonoidHom (maxProPQuotient 2 GammaA)
      (maxProPQuotient 2 GammaA ⧸ V.toSubgroup) := quotientMk V.toSubgroup with hqdef
  set g : ContinuousMonoidHom (FreeProfiniteGroup (Fin 4))
      (maxProPQuotient 2 GammaA ⧸ V.toSubgroup) := q.comp (mk.comp (quotientMk NA)) with hgdef
  have h2grp : IsPGroup 2 (maxProPQuotient 2 GammaA ⧸ V.toSubgroup) := maxProPGammaA_isProP V
  have ho : ∀ x : maxProPQuotient 2 GammaA ⧸ V.toSubgroup, powOmega2 x = x := fun x => by
    obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.mp h2grp) x
    exact powOmega2_eq_self_of_orderOf_two_pow hk
  have hgτ : g univMarking.τ = 1 := by
    show q (mk (quotientMk NA univMarking.τ)) = 1
    rw [show mk (quotientMk NA univMarking.τ) = mk gammaTau from rfl, maxProPMk_gammaTau, map_one]
  -- the pushed marking satisfies (6) (kills `wildRelator`), and `τ ↦ 1`
  have h0w : quotientMk NA univMarking.wildRelator = (1 : GammaA) :=
    (quotientMk_eq_one_iff NA).mpr wildRelator_mem_NA
  have hkill : g.toMonoidHom univMarking.wildRelator = 1 := by
    show q (mk (quotientMk NA univMarking.wildRelator)) = 1
    rw [h0w, map_one, map_one]
  have hwild : (univMarking.map g.toMonoidHom).WildRel :=
    (Marking.map_wildRelator_eq_one_iff g univMarking).mp hkill
  have ht : univMarking.map g.toMonoidHom
      = Marking.mk (q (mk gammaSigma)) 1 (q (mk gammaX0)) (q (mk gammaX1)) := by
    have cσ : g.toMonoidHom univMarking.σ = q (mk gammaSigma) := by rw [hgdef]; rfl
    have cτ : g.toMonoidHom univMarking.τ = 1 := hgτ
    have cx0 : g.toMonoidHom univMarking.x₀ = q (mk gammaX0) := by rw [hgdef]; rfl
    have cx1 : g.toMonoidHom univMarking.x₁ = q (mk gammaX1) := by rw [hgdef]; rfl
    rw [show univMarking.map g.toMonoidHom = Marking.mk (g.toMonoidHom univMarking.σ)
        (g.toMonoidHom univMarking.τ) (g.toMonoidHom univMarking.x₀)
        (g.toMonoidHom univMarking.x₁) from rfl, Marking.mk.injEq]
    exact ⟨cσ, cτ, cx0, cx1⟩
  rw [ht, wildRel_iff_piRelatorWord (q (mk gammaSigma)) (q (mk gammaX0)) (q (mk gammaX1))
    (ho _) (ho _) (ho _)] at hwild
  refine (quotientMk_eq_one_iff V.toSubgroup).mp ?_
  have hpull : q (conjP (mk gammaX0) ((mk gammaSigma) ^ 2) * mk gammaX0
        * commP (mk gammaX1) (mk gammaSigma))
      = conjP (q (mk gammaX0)) ((q (mk gammaSigma)) ^ 2) * q (mk gammaX0)
        * commP (q (mk gammaX1)) (q (mk gammaSigma)) := by
    simp only [conjP, commP, map_mul, map_inv, map_pow]
  rw [hpull]; exact hwild

/-! ## The marked isomorphism `Γ_A(2) ≅ Π` (Prop 3.10, `Γ_A` half) -/

/-- The forward map `Φ : Γ_A(2) → Π`, the descent of `φ_Π` through the maximal pro-`2` quotient
(`Π` is pro-`2`, so `φ_Π` kills `proPKernel`). -/
noncomputable def PhiMax : ContinuousMonoidHom (maxProPQuotient 2 GammaA) PiBd :=
  quotientLift (proPKernel 2 GammaA) phiP (proPKernel_le_ker piBd_isProP phiP)

@[simp] lemma PhiMax_mk_gammaSigma : PhiMax (maxProPMk 2 GammaA gammaSigma) = piSigma :=
  (quotientLift_quotientMk _ _ _ _).trans phiP_gammaSigma

@[simp] lemma PhiMax_mk_gammaX0 : PhiMax (maxProPMk 2 GammaA gammaX0) = piX0 :=
  (quotientLift_quotientMk _ _ _ _).trans phiP_gammaX0

@[simp] lemma PhiMax_mk_gammaX1 : PhiMax (maxProPMk 2 GammaA gammaX1) = piX1 :=
  (quotientLift_quotientMk _ _ _ _).trans phiP_gammaX1

@[simp] lemma PhiMax_mk_gammaTau : PhiMax (maxProPMk 2 GammaA gammaTau) = 1 :=
  (quotientLift_quotientMk _ _ _ _).trans phiP_gammaTau

/-- The backward base map `F₃ → Γ_A(2)`, `σ ↦ [σ], x₀ ↦ [x₀], x₁ ↦ [x₁]`. -/
noncomputable def psiBase : FreeProfiniteGroup (Fin 3) ⟶ maxProPQuotient 2 GammaA :=
  (FreeProfiniteGroup.homEquiv (Fin 3) (maxProPQuotient 2 GammaA)).symm
    ![maxProPMk 2 GammaA gammaSigma, maxProPMk 2 GammaA gammaX0, maxProPMk 2 GammaA gammaX1]

@[simp] lemma psiBase_of0 :
    psiBase.hom.toMonoidHom (FreeProfiniteGroup.of 0) = maxProPMk 2 GammaA gammaSigma :=
  FreeProfiniteGroup.homEquiv_symm_of _ _ _
@[simp] lemma psiBase_of1 :
    psiBase.hom.toMonoidHom (FreeProfiniteGroup.of 1) = maxProPMk 2 GammaA gammaX0 :=
  FreeProfiniteGroup.homEquiv_symm_of _ _ _
@[simp] lemma psiBase_of2 :
    psiBase.hom.toMonoidHom (FreeProfiniteGroup.of 2) = maxProPMk 2 GammaA gammaX1 :=
  FreeProfiniteGroup.homEquiv_symm_of _ _ _

/-- The base map kills `piRelator` (that is the backward collapse `piRelatorWord_maxA_eq_one`). -/
theorem psiBase_piRelator : psiBase.hom.toMonoidHom piRelator = 1 := by
  have hword : psiBase.hom.toMonoidHom piRelator
      = conjP (maxProPMk 2 GammaA gammaX0) ((maxProPMk 2 GammaA gammaSigma) ^ 2)
        * maxProPMk 2 GammaA gammaX0
        * commP (maxProPMk 2 GammaA gammaX1) (maxProPMk 2 GammaA gammaSigma) := by
    simp only [piRelator, conjP, commP, map_mul, map_inv, map_pow, psiBase_of0, psiBase_of1,
      psiBase_of2]
  rw [hword, piRelatorWord_maxA_eq_one]

/-- The lift through the presentation `Π(pre) → Γ_A(2)`. -/
noncomputable def psiPres :
    ContinuousMonoidHom (profinitePresentation {piRelator}) (maxProPQuotient 2 GammaA) :=
  presentationLift {piRelator} psiBase.hom fun r hr => by rcases hr with rfl; exact psiBase_piRelator

/-- The backward map `Ψ : Π → Γ_A(2)` (through the max pro-`2` universal property). -/
noncomputable def PsiMax : ContinuousMonoidHom PiBd (maxProPQuotient 2 GammaA) :=
  quotientLift (proPKernel 2 (profinitePresentation {piRelator})) psiPres
    (proPKernel_le_ker maxProPGammaA_isProP psiPres)

@[simp] lemma PsiMax_piSigma : PsiMax piSigma = maxProPMk 2 GammaA gammaSigma := by
  show PsiMax (maxProPMk 2 (profinitePresentation {piRelator})
    (quotientMk (relatorSubgroup {piRelator}) (FreeProfiniteGroup.of 0))) = _
  rw [show PsiMax (maxProPMk 2 (profinitePresentation {piRelator})
      (quotientMk (relatorSubgroup {piRelator}) (FreeProfiniteGroup.of 0)))
      = psiPres (quotientMk (relatorSubgroup {piRelator}) (FreeProfiniteGroup.of 0)) from
    quotientLift_quotientMk _ _ _ _,
    show psiPres (quotientMk (relatorSubgroup {piRelator}) (FreeProfiniteGroup.of 0))
      = psiBase.hom (FreeProfiniteGroup.of 0) from presentationLift_mk _ _ _ _]
  exact psiBase_of0

@[simp] lemma PsiMax_piX0 : PsiMax piX0 = maxProPMk 2 GammaA gammaX0 := by
  show PsiMax (maxProPMk 2 (profinitePresentation {piRelator})
    (quotientMk (relatorSubgroup {piRelator}) (FreeProfiniteGroup.of 1))) = _
  rw [show PsiMax (maxProPMk 2 (profinitePresentation {piRelator})
      (quotientMk (relatorSubgroup {piRelator}) (FreeProfiniteGroup.of 1)))
      = psiPres (quotientMk (relatorSubgroup {piRelator}) (FreeProfiniteGroup.of 1)) from
    quotientLift_quotientMk _ _ _ _,
    show psiPres (quotientMk (relatorSubgroup {piRelator}) (FreeProfiniteGroup.of 1))
      = psiBase.hom (FreeProfiniteGroup.of 1) from presentationLift_mk _ _ _ _]
  exact psiBase_of1

@[simp] lemma PsiMax_piX1 : PsiMax piX1 = maxProPMk 2 GammaA gammaX1 := by
  show PsiMax (maxProPMk 2 (profinitePresentation {piRelator})
    (quotientMk (relatorSubgroup {piRelator}) (FreeProfiniteGroup.of 2))) = _
  rw [show PsiMax (maxProPMk 2 (profinitePresentation {piRelator})
      (quotientMk (relatorSubgroup {piRelator}) (FreeProfiniteGroup.of 2)))
      = psiPres (quotientMk (relatorSubgroup {piRelator}) (FreeProfiniteGroup.of 2)) from
    quotientLift_quotientMk _ _ _ _,
    show psiPres (quotientMk (relatorSubgroup {piRelator}) (FreeProfiniteGroup.of 2))
      = psiBase.hom (FreeProfiniteGroup.of 2) from presentationLift_mk _ _ _ _]
  exact psiBase_of2

/-- `Γ_A(2)` is topologically generated by the images of the four marked generators. -/
theorem topGen_maxA :
    (Subgroup.closure {maxProPMk 2 GammaA gammaSigma, maxProPMk 2 GammaA gammaTau,
      maxProPMk 2 GammaA gammaX0, maxProPMk 2 GammaA gammaX1}).topologicalClosure = ⊤ := by
  have h := topGen_map
    (f := ((maxProPMk 2 GammaA).comp (quotientMk NA)).toMonoidHom)
    ((maxProPMk 2 GammaA).comp (quotientMk NA)).continuous_toFun
    ((quotientMk_surjective (proPKernel 2 GammaA)).comp (quotientMk_surjective NA))
    (topGen_freeProfiniteGroup (Fin 4))
  have h1 : (⇑((maxProPMk 2 GammaA).comp (quotientMk NA)).toMonoidHom)
      '' Set.range (FreeProfiniteGroup.of (X := Fin 4))
      = {maxProPMk 2 GammaA gammaSigma, maxProPMk 2 GammaA gammaTau,
         maxProPMk 2 GammaA gammaX0, maxProPMk 2 GammaA gammaX1} := by
    rw [← Set.range_comp]
    ext z; constructor
    · rintro ⟨i, rfl⟩; fin_cases i
      · exact Set.mem_insert _ _
      · exact Set.mem_insert_of_mem _ (Set.mem_insert _ _)
      · exact Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_insert _ _))
      · exact Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ rfl))
    · rintro (rfl | rfl | rfl | rfl)
      exacts [⟨0, rfl⟩, ⟨1, rfl⟩, ⟨2, rfl⟩, ⟨3, rfl⟩]
  rwa [h1] at h

/-- `Φ ∘ Ψ = id` on `Π` (both fix `πσ, πx₀, πx₁`; density). -/
theorem PhiMax_PsiMax (x : PiBd) : PhiMax (PsiMax x) = x := by
  have h := monoidHom_eq_of_topGen
    (f := PhiMax.toMonoidHom.comp PsiMax.toMonoidHom) (g := MonoidHom.id PiBd)
    (by rw [MonoidHom.coe_comp]
        exact PhiMax.continuous_toFun.comp PsiMax.continuous_toFun) continuous_id
    topGen_piBd ?_
  · exact h x
  · rintro z (rfl | rfl | rfl) <;> simp

/-- `Ψ ∘ Φ = id` on `Γ_A(2)` (checked on the four marked generator images; density). -/
theorem PsiMax_PhiMax (x : maxProPQuotient 2 GammaA) : PsiMax (PhiMax x) = x := by
  have h := monoidHom_eq_of_topGen
    (f := PsiMax.toMonoidHom.comp PhiMax.toMonoidHom) (g := MonoidHom.id _)
    (by rw [MonoidHom.coe_comp]
        exact PsiMax.continuous_toFun.comp PhiMax.continuous_toFun) continuous_id
    topGen_maxA ?_
  · exact h x
  · rintro z (rfl | rfl | rfl | rfl) <;> simp [maxProPMk_gammaTau]

/-- **The marked isomorphism `Γ_A(2) ≅ Π`** (Prop 3.10, `Γ_A` half). -/
noncomputable def maxAEquiv : ContinuousMulEquiv (maxProPQuotient 2 GammaA) PiBd where
  toFun := PhiMax
  invFun := PsiMax
  left_inv := PsiMax_PhiMax
  right_inv := PhiMax_PsiMax
  map_mul' := map_mul PhiMax
  continuous_toFun := PhiMax.continuous_toFun
  continuous_invFun := PsiMax.continuous_toFun

/-- **Prop 3.10, `Γ_A` half** (proved): the maximal pro-`2` quotient of `Γ_A` is `Π`, matching
the marked generators. -/
theorem prop_3_10_gammaA_proved :
    ∃ e : ContinuousMulEquiv (maxProPQuotient 2 GammaA) PiBd,
      e (maxProPMk 2 GammaA (quotientMk NA univMarking.σ)) = piSigma ∧
      e (maxProPMk 2 GammaA (quotientMk NA univMarking.τ)) = 1 ∧
      e (maxProPMk 2 GammaA (quotientMk NA univMarking.x₀)) = piX0 ∧
      e (maxProPMk 2 GammaA (quotientMk NA univMarking.x₁)) = piX1 :=
  ⟨maxAEquiv, PhiMax_mk_gammaSigma, PhiMax_mk_gammaTau, PhiMax_mk_gammaX0, PhiMax_mk_gammaX1⟩

/-- `Γ_A` is topologically generated by its four marked generators. -/
theorem topGen_gammaA :
    (Subgroup.closure {gammaSigma, gammaTau, gammaX0, gammaX1}).topologicalClosure = ⊤ := by
  have h := topGen_map (f := (quotientMk NA).toMonoidHom) (quotientMk NA).continuous_toFun
    (quotientMk_surjective NA) (topGen_freeProfiniteGroup (Fin 4))
  have h1 : (⇑(quotientMk NA).toMonoidHom) '' Set.range (FreeProfiniteGroup.of (X := Fin 4))
      = {gammaSigma, gammaTau, gammaX0, gammaX1} := by
    rw [← Set.range_comp]
    ext z; constructor
    · rintro ⟨i, rfl⟩; fin_cases i
      · exact Set.mem_insert _ _
      · exact Set.mem_insert_of_mem _ (Set.mem_insert _ _)
      · exact Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_insert _ _))
      · exact Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ rfl))
    · rintro (rfl | rfl | rfl | rfl)
      exacts [⟨0, rfl⟩, ⟨1, rfl⟩, ⟨2, rfl⟩, ⟨3, rfl⟩]
  rwa [h1] at h

end SectionThree

end GQ2

/-! ### Paper-tag ledger (auto-generated by paperforge; do not edit)

  * Cor 3.12 = ⟦cor-relativeDemushkin⟧
  * eq. (27) = ⟦eq-boundarymap⟧
  * Lemma 3.1 = ⟦lem-tamefinite⟧
  * Prop 3.10 = ⟦prop-pro2⟧
  * Prop 3.14 = ⟦prop-compatiblemarking⟧
  * Prop 3.2 = ⟦prop-tamequotient⟧
-/
