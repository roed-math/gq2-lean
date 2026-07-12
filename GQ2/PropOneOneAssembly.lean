import GQ2.AnabelianBridge
import GQ2.Orientation
import GQ2.Foundations.Axioms

/-!
# Proposition 1.1 — the assembly  (ticket P-10)

`GQ2/PropOneOne.lean` supplied the `ν_ur`-descent infrastructure; this file assembles the marked
isomorphism itself.  Paper: *"there exist topological generators `a, s, y` of `D = G_{ℚ₂}(2)` with
`D ≅ ⟨a,s,y | a²s⁴[s,y]⟩` and `ν_ur(a,s,y) = (−2,1,0)`."*

## Proof structure (paper §3, "composes B3c/B4 with Lemma 3.5 and Prop. 3.8")

* **B3c** (`dyadicOrientation`) provides a *group* isomorphism `equiv : G_{ℚ₂}(2) ≅ D₀` whose
  descended cyclotomic character `chiTwo` takes the marked values `(−1, 1, (−3)⁻¹)` on `A, S, Y`.
* **Lemma 3.5** (`lemma_3_5_marked_abelianization`, ticket P-07) provides an *abelianization*
  isomorphism `e_ab : D₀^{ab} ≅ G_{ℚ₂}(2)^{ab}` sending `Ā, S̄, Ȳ` to the reciprocity classes
  `π(rec −4), π(rec 1/2), π(rec −3)` — which carry the `ν_ur`-row `(−2, 1, 0)`.
* The two isomorphisms need not agree on abelianizations; they differ by a `χ`-preserving
  automorphism `Θ` of `D₀^{ab}`, which by **Prop. 3.8** (P-08: `prop_3_8_classification` +
  `prop_3_8_lift`) is some `α_{u,b}` and hence **lifts** to a group automorphism `Ψ` of `D₀`.
  Then `e := Ψ ∘ equiv` induces `e_ab` on abelianizations, so `e.symm(A/S/Y)` have the marked
  reciprocity classes, and the `ν_ur`-rows read off through `nu_ur_recip_*`.

`e_ab` is Lemma 3.5, whose sole gap is the census-gated `markedHom_bijective` (Escalation 5); so
`prop_1_1` inherits exactly that one sorry and nothing else.  Everything here (functorial
abelianization, the `χ`-descent, the `Θ`-classification/lift, the `ν_ur`-readoff) is otherwise
`std-3 + B3c + B8`.
-/

open scoped Classical

namespace GQ2

open SectionThree

/-! ## Functorial abelianization of a continuous isomorphism

The repo's `topAbelianization` (`G ⧸ closure⁅G,G⁆`) is not packaged as a functor; we supply just
enough — the pushforward of a continuous hom, and its promotion to an equivalence — for the
comparison `e_ab` vs `equiv`.  As elsewhere (`SectionThree`, `AnabelianBridge`) the
`CommGroup`/`Compact`/`T2`/`TotDisc` instances on `topAbelianization` are file-local. -/

noncomputable local instance instCommGroupTopAbP10 {G : Type*} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] : CommGroup (topAbelianization G) where
  __ := (inferInstance : Group (topAbelianization G))
  mul_comm := by
    intro x y
    obtain ⟨a, rfl⟩ := abMk_surjective (G := G) x
    obtain ⟨b, rfl⟩ := abMk_surjective (G := G) y
    rw [← map_mul, ← map_mul]
    show QuotientGroup.mk (a * b) = QuotientGroup.mk (b * a)
    refine QuotientGroup.eq.mpr ?_
    rw [show (a * b)⁻¹ * (b * a) = b⁻¹ * a⁻¹ * b * a by group]
    apply Subgroup.le_topologicalClosure
    rw [commutator_def]
    simpa [commutatorElement_def] using Subgroup.commutator_mem_commutator (G := G)
      (Subgroup.mem_top b⁻¹) (Subgroup.mem_top a⁻¹)

local instance instCompactSpaceTopAbP10 {G : Type*} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G] :
    CompactSpace (topAbelianization G) :=
  inferInstanceAs (CompactSpace (G ⧸ (commutator G).topologicalClosure))

local instance instT2SpaceTopAbP10 {G : Type*} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G] :
    T2Space (topAbelianization G) :=
  haveI : IsClosed ((commutator G).topologicalClosure : Set G) :=
    (commutator G).isClosed_topologicalClosure
  inferInstanceAs (T2Space (G ⧸ (commutator G).topologicalClosure))

local instance instTotallyDisconnectedSpaceTopAbP10 {G : Type*} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G] :
    TotallyDisconnectedSpace (topAbelianization G) :=
  haveI : IsClosed ((commutator G).topologicalClosure : Set G) :=
    (commutator G).isClosed_topologicalClosure
  inferInstanceAs (TotallyDisconnectedSpace (G ⧸ (commutator G).topologicalClosure))

section FunctorialAb

variable {G H : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
  [CompactSpace H] [T2Space H] [TotallyDisconnectedSpace H]

/-- Pushforward of a continuous hom `f : G → H` to the topological abelianizations,
`abMk g ↦ abMk (f g)` (well-defined: `abMk_H ∘ f` kills `closure⁅G,G⁆`). -/
noncomputable def topAbLiftHom (f : ContinuousMonoidHom G H) :
    ContinuousMonoidHom (topAbelianization G) (topAbelianization H) :=
  ⟨QuotientGroup.lift (commutator G).topologicalClosure ((abMk (G := H)).comp f.toMonoidHom) (by
      refine Subgroup.topologicalClosure_minimal _ (Abelianization.commutator_subset_ker _) ?_
      rw [MonoidHom.coe_ker]
      exact isClosed_singleton.preimage (continuous_abMk.comp f.continuous_toFun)),
    (QuotientGroup.isQuotientMap_mk _).continuous_iff.mpr (continuous_abMk.comp f.continuous_toFun)⟩

@[simp] lemma topAbLiftHom_abMk (f : ContinuousMonoidHom G H) (g : G) :
    topAbLiftHom f (abMk g) = abMk (f g) := rfl

end FunctorialAb

/-- Functorial abelianization of a continuous isomorphism `φ : G ≅ H`. -/
noncomputable def topAbCongr {G H : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
    [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [CompactSpace H] [T2Space H] [TotallyDisconnectedSpace H]
    (φ : ContinuousMulEquiv G H) :
    ContinuousMulEquiv (topAbelianization G) (topAbelianization H) :=
  continuousMulEquivOfBijective
    (topAbLiftHom ⟨φ.toMulEquiv.toMonoidHom, φ.continuous_toFun⟩)
    (Function.bijective_iff_has_inverse.mpr
      ⟨topAbLiftHom ⟨φ.symm.toMulEquiv.toMonoidHom, φ.symm.continuous_toFun⟩,
        fun x => by
          obtain ⟨g, rfl⟩ := abMk_surjective (G := G) x
          simp only [topAbLiftHom_abMk]
          exact congrArg abMk (φ.symm_apply_apply g),
        fun x => by
          obtain ⟨h, rfl⟩ := abMk_surjective (G := H) x
          simp only [topAbLiftHom_abMk]
          exact congrArg abMk (φ.apply_symm_apply h)⟩)

@[simp] lemma topAbCongr_abMk {G H : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
    [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [CompactSpace H] [T2Space H] [TotallyDisconnectedSpace H]
    (φ : ContinuousMulEquiv G H) (g : G) :
    topAbCongr φ (abMk g) = abMk (φ g) := rfl

@[simp] lemma topAbCongr_symm_abMk {G H : Type*} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
    [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [CompactSpace H] [T2Space H] [TotallyDisconnectedSpace H]
    (φ : ContinuousMulEquiv G H) (h : H) :
    (topAbCongr φ).symm (abMk h) = abMk (φ.symm h) := by
  refine (topAbCongr φ).injective ?_
  rw [ContinuousMulEquiv.apply_symm_apply, topAbCongr_abMk, ContinuousMulEquiv.apply_symm_apply]

/-- Descent of a continuous hom `f : G → A` (`A` abelian Hausdorff) through `abMk`. -/
noncomputable def abDescend {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    {A : Type*} [CommGroup A] [TopologicalSpace A] [IsTopologicalGroup A] [T2Space A]
    (f : ContinuousMonoidHom G A) : ContinuousMonoidHom (topAbelianization G) A :=
  ⟨QuotientGroup.lift (commutator G).topologicalClosure f.toMonoidHom (by
      refine Subgroup.topologicalClosure_minimal _ (Abelianization.commutator_subset_ker _) ?_
      rw [MonoidHom.coe_ker]
      exact isClosed_singleton.preimage f.continuous_toFun),
    (QuotientGroup.isQuotientMap_mk _).continuous_iff.mpr f.continuous_toFun⟩


/-- **Extensionality for `D₀^{ab}` homs into a pro-2 group**: two continuous homs agreeing on
`Ā, S̄, Ȳ` agree everywhere (every element is `Ā^a S̄^s Ȳ^y` by `D0ab_coord`, and continuous homs
commute with `zpowZtwo`). -/
lemma d0ab_hom_ext {A : Type} [Group A] [TopologicalSpace A] [IsTopologicalGroup A]
    [CompactSpace A] [T2Space A] [TotallyDisconnectedSpace A]
    (hA : IsProP 2 A) (φ ψ : ContinuousMonoidHom (topAbelianization (D0 : Type)) A)
    (hAgen : φ (abMk d0A) = ψ (abMk d0A)) (hS : φ (abMk d0S) = ψ (abMk d0S))
    (hY : φ (abMk d0Y) = ψ (abMk d0Y)) (z : topAbelianization (D0 : Type)) : φ z = ψ z := by
  obtain ⟨a, s, y, rfl⟩ := D0ab_coord z
  rw [map_mul, map_mul, map_mul, map_mul,
    map_zpowZtwo isProP_two_topAb_D0 hA φ (abMk d0A) a,
    map_zpowZtwo isProP_two_topAb_D0 hA φ (abMk d0S) s,
    map_zpowZtwo isProP_two_topAb_D0 hA φ (abMk d0Y) y,
    map_zpowZtwo isProP_two_topAb_D0 hA ψ (abMk d0A) a,
    map_zpowZtwo isProP_two_topAb_D0 hA ψ (abMk d0S) s,
    map_zpowZtwo isProP_two_topAb_D0 hA ψ (abMk d0Y) y, hAgen, hS, hY]

/-! ## The assembly -/

section Assembly

open SectionThree PropOneOne

variable [CompactSpace AbsGalQ2] [TotallyDisconnectedSpace AbsGalQ2]

/-- The B3c dyadic-orientation bundle (a fixed witness of the axiom `dyadicOrientation`). -/
noncomputable def orientBundle : DyadicOrientation := dyadicOrientation

/-- `χ` transported to `D₀^{ab}`: `chiD0 (abMk d) = chiTwo (equiv.symm d)`.  Its generator values
are `(−1, 1, (−3)⁻¹)` (`orientBundle.chi_A/S/Y`). -/
noncomputable def chiD0 : ContinuousMonoidHom (topAbelianization (D0 : Type)) ℤ_[2]ˣ :=
  abDescend ⟨orientBundle.chiTwo.comp orientBundle.equiv.symm.toMulEquiv.toMonoidHom,
    orientBundle.continuous_chiTwo.comp orientBundle.equiv.symm.continuous_toFun⟩

/-- `χ` on `G_{ℚ₂}(2)^{ab}`: `chiG (abMk h) = chiTwo h`. -/
noncomputable def chiG :
    ContinuousMonoidHom (topAbelianization (maxProPQuotient 2 AbsGalQ2)) ℤ_[2]ˣ :=
  abDescend ⟨orientBundle.chiTwo, orientBundle.continuous_chiTwo⟩

@[simp] lemma chiD0_abMk (d : (D0 : Type)) :
    chiD0 (abMk d) = orientBundle.chiTwo (orientBundle.equiv.symm d) := rfl

@[simp] lemma chiG_abMk (h : (maxProPQuotient 2 AbsGalQ2 : Type)) :
    chiG (abMk h) = orientBundle.chiTwo h := rfl

lemma chiD0_A : chiD0 (abMk d0A) = -1 := orientBundle.chi_A
lemma chiD0_S : chiD0 (abMk d0S) = 1 := orientBundle.chi_S
lemma chiD0_Y (y : ℤ_[2]ˣ) (hy : (y : ℤ_[2]) = -3) : chiD0 (abMk d0Y) = y⁻¹ :=
  orientBundle.chi_Y y hy

/-- `χ_G ∘ markedPi = chiCycAb`: the cyclotomic values agree with `markedPi`'s reciprocity classes
(via `chiTwo_factors`). -/
lemma chiG_markedPi (x : AbsGalQ2ab) : chiG (markedPi x) = chiCycAb x := by
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective x
  show chiG (markedPi (toAb g)) = chiCycAb (toAb g)
  rw [markedPi_toAb, chiG_abMk, orientBundle.chiTwo_factors, chiCycAb_toAb]

/-- `chiD0 ∘ (topAbCongr equiv) = chiG`. -/
lemma chiD0_equivAb (w : topAbelianization (maxProPQuotient 2 AbsGalQ2)) :
    chiD0 (topAbCongr orientBundle.equiv w) = chiG w := by
  obtain ⟨h, rfl⟩ := abMk_surjective (G := (maxProPQuotient 2 AbsGalQ2 : Type)) w
  rw [topAbCongr_abMk, chiD0_abMk, chiG_abMk, ContinuousMulEquiv.symm_apply_apply]

variable (R : LocalReciprocity)

/-- `ν_ur` descended to `G_{ℚ₂}(2)^{ab}` (through `abMk`). -/
noncomputable def nuUrBarAb :
    ContinuousMonoidHom (topAbelianization (maxProPQuotient 2 AbsGalQ2)) (Multiplicative ℤ_[2]) :=
  abDescend (nuUrBar R)

/-- `ν_ur = nuUrBarAb ∘ markedPi`: the unramified coordinate reads off `markedPi`'s classes. -/
lemma nu_ur_eq_nuUrBarAb_markedPi (x : AbsGalQ2ab) :
    R.nu_ur x = nuUrBarAb R (markedPi x) := by
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective x
  show R.nu_ur (toAb g) = nuUrBarAb R (markedPi (toAb g))
  rw [markedPi_toAb]
  show R.nu_ur (toAb g) = nuUrBar R (maxProPMk 2 AbsGalQ2 g)
  rw [nuUrBar_maxProPMk]

/-! ### Reciprocity values of the marked classes (`std-3 + B5`)

These consume only the bundle `R`, not the compactness of `AbsGalQ2`. -/

omit [CompactSpace AbsGalQ2] [TotallyDisconnectedSpace AbsGalQ2] in
/-- `ν_ur(rec(−4)) = −2`. -/
lemma nu_ur_recip_unitNeg4 :
    R.nu_ur (R.recip unitNeg4) = Multiplicative.ofAdd ((-2 : ℤ) : ℤ_[2]) := by
  have hv : v2 unitNeg4 = 2 := by
    simp only [v2, unitNeg4, Units.val_mk0]
    rw [show (-4 : ℚ_[2]) = ((-4 : ℤ) : ℚ_[2]) by push_cast; ring, Padic.valuation_intCast,
      padicValInt, show (-4 : ℤ).natAbs = 2 ^ 2 from rfl, padicValNat.prime_pow]
    norm_cast
  rw [R.nu_ur_recip, hv]

omit [CompactSpace AbsGalQ2] [TotallyDisconnectedSpace AbsGalQ2] in
/-- `ν_ur(rec(2)) = −1`. -/
lemma nu_ur_recip_uniformizer' :
    R.nu_ur (R.recip uniformizer) = Multiplicative.ofAdd ((-1 : ℤ) : ℤ_[2]) := by
  rw [R.nu_ur_recip]
  norm_num [v2, uniformizer, Padic.valuation_p]

omit [CompactSpace AbsGalQ2] [TotallyDisconnectedSpace AbsGalQ2] in
/-- `ν_ur(rec(−3)) = 0`. -/
lemma nu_ur_recip_unitNeg3 :
    R.nu_ur (R.recip unitNeg3) = Multiplicative.ofAdd ((0 : ℤ) : ℤ_[2]) := by
  have hv : v2 unitNeg3 = 0 := by
    simp only [v2, unitNeg3, Units.val_mk0]
    rw [show (-3 : ℚ_[2]) = ((-3 : ℤ) : ℚ_[2]) by push_cast; ring, Padic.valuation_intCast]
    simp [padicValInt]
  rw [R.nu_ur_recip, hv]
  norm_num

/-- A unit of value `−3`. -/
noncomputable def unitNegThree : ℤ_[2]ˣ := (isUnit_intCast_of_odd (⟨-2, by ring⟩ : Odd (-3 : ℤ))).unit

omit [CompactSpace AbsGalQ2] [TotallyDisconnectedSpace AbsGalQ2] in
@[simp] lemma unitNegThree_val : (unitNegThree : ℤ_[2]) = -3 := by
  rw [unitNegThree, IsUnit.unit_spec]; push_cast; ring

omit [CompactSpace AbsGalQ2] [TotallyDisconnectedSpace AbsGalQ2] in
/-- `chiCycAb(rec(−4)) = −1`. -/
lemma chiCycAb_recip_unitNeg4 : chiCycAb (R.recip unitNeg4) = (-1 : ℤ_[2]ˣ) := by
  have hdecomp : unitNeg4 = unitEmbed (-1) * uniformizer ^ 2 := by
    ext
    simp only [unitNeg4, uniformizer, Units.val_mul, Units.val_pow_eq_pow_val, unitEmbed_val,
      Units.val_mk0, Units.val_neg, Units.val_one, map_neg, map_one]
    ring
  rw [hdecomp, map_mul, map_pow, map_mul, map_pow, R.chiCyc_recip_unit, R.chiCyc_recip_uniformizer]
  simp

omit [CompactSpace AbsGalQ2] [TotallyDisconnectedSpace AbsGalQ2] in
/-- `chiCycAb(rec(−3)) = unitNegThree⁻¹`. -/
lemma chiCycAb_recip_unitNeg3 : chiCycAb (R.recip unitNeg3) = unitNegThree⁻¹ := by
  have hval : unitNeg3 = unitEmbed unitNegThree := by
    apply Units.ext
    show (-3 : ℚ_[2]) = algebraMap ℤ_[2] ℚ_[2] (unitNegThree : ℤ_[2])
    rw [unitNegThree_val, map_neg, map_ofNat]
  rw [hval, R.chiCyc_recip_unit]

/-! ### Proposition 1.1 -/

/-- **Proposition 1.1** (ticket P-10).  A marked isomorphism `e : G_{ℚ₂}(2) ≅ D₀` with unramified
coordinates `ν_ur(a, s, y) = (−2, 1, 0)`.  Assembled from B3c (`orientBundle.equiv`), Lemma 3.5
(`lemma_3_5_marked_abelianization`, ticket P-07 — its sole gap `markedHom_bijective` is inherited),
and Prop. 3.8 (`prop_3_8_classification`/`prop_3_8_lift`, ticket P-08).  Statement moved here from
`GQ2/SectionThree.lean` (comment-pointer there), P-09 precedent. -/
theorem SectionThree.prop_1_1 :
    ∃ e : ContinuousMulEquiv (maxProPQuotient 2 AbsGalQ2) D0,
      (∀ g : AbsGalQ2, maxProPMk 2 AbsGalQ2 g = e.symm d0A →
        R.nu_ur (toAb g) = Multiplicative.ofAdd ((-2 : ℤ) : ℤ_[2])) ∧
      (∀ g : AbsGalQ2, maxProPMk 2 AbsGalQ2 g = e.symm d0S →
        R.nu_ur (toAb g) = Multiplicative.ofAdd ((1 : ℤ) : ℤ_[2])) ∧
      (∀ g : AbsGalQ2, maxProPMk 2 AbsGalQ2 g = e.symm d0Y →
        R.nu_ur (toAb g) = Multiplicative.ofAdd ((0 : ℤ) : ℤ_[2])) := by
  obtain ⟨B⟩ := b_decomposition
  obtain ⟨eab, hA5, hS5, hY5⟩ := lemma_3_5_marked_abelianization R
  -- marked values of `eab` (resolve the lift quantifier via surjectivity of `toAb`)
  have eabA : eab (abMk d0A) = markedPi (R.recip unitNeg4) := by
    obtain ⟨g, hg'⟩ : ∃ g, toAb g = R.recip unitNeg4 := QuotientGroup.mk_surjective _
    rw [hA5 g hg', ← markedPi_toAb, hg']
  have eabS : eab (abMk d0S) = (markedPi (R.recip uniformizer))⁻¹ := by
    obtain ⟨g, hg'⟩ : ∃ g, toAb g = (R.recip uniformizer)⁻¹ := QuotientGroup.mk_surjective _
    rw [hS5 g hg', ← markedPi_toAb, hg', map_inv]
  have eabY : eab (abMk d0Y) = markedPi (R.recip unitNeg3) := by
    obtain ⟨g, hg'⟩ : ∃ g, toAb g = R.recip unitNeg3 := QuotientGroup.mk_surjective _
    rw [hY5 g hg', ← markedPi_toAb, hg']
  -- the comparison automorphism `Θ = (topAbCongr equiv) ∘ eab`, χ-preserving
  set Θ : ContinuousMulEquiv (topAbelianization (D0 : Type)) (topAbelianization (D0 : Type)) :=
    eab.trans (topAbCongr orientBundle.equiv) with hΘ
  have hchiGeab : ∀ z, chiG (eab z) = chiD0 z := by
    refine d0ab_hom_ext isProP_two_unitsPadicInt
      (chiG.comp ⟨eab.toMulEquiv.toMonoidHom, eab.continuous_toFun⟩) chiD0 ?_ ?_ ?_
    · show chiG (eab (abMk d0A)) = chiD0 (abMk d0A)
      rw [eabA, chiG_markedPi, chiCycAb_recip_unitNeg4, chiD0_A]
    · show chiG (eab (abMk d0S)) = chiD0 (abMk d0S)
      rw [eabS, map_inv, chiG_markedPi, R.chiCyc_recip_uniformizer, chiD0_S, inv_one]
    · show chiG (eab (abMk d0Y)) = chiD0 (abMk d0Y)
      rw [eabY, chiG_markedPi, chiCycAb_recip_unitNeg3, chiD0_Y unitNegThree unitNegThree_val]
  have hΘpres : ∀ x, chiD0 (Θ x) = chiD0 x := by
    intro x
    show chiD0 (topAbCongr orientBundle.equiv (eab x)) = chiD0 x
    rw [chiD0_equivAb, hchiGeab]
  -- classify Θ and lift it to a group automorphism `Ψ` of `D₀`
  obtain ⟨⟨u, b⟩, ⟨hΘA, hΘS, hΘY⟩, -⟩ :=
    SectionThree.prop_3_8_classification B Θ chiD0.toMonoidHom chiD0.continuous_toFun
      chiD0_A chiD0_S (fun y hy => chiD0_Y y hy) hΘpres
  obtain ⟨Ψ, hΨA, hΨS, hΨY⟩ := SectionThree.prop_3_8_lift B u b
  -- `topAbCongr Ψ = Θ`, matched on generators through `B.e`
  have hΨΘ : ∀ z, topAbCongr Ψ z = Θ z := by
    refine d0ab_hom_ext isProP_two_topAb_D0
      ⟨(topAbCongr Ψ).toMulEquiv.toMonoidHom, (topAbCongr Ψ).continuous_toFun⟩
      ⟨Θ.toMulEquiv.toMonoidHom, Θ.continuous_toFun⟩ ?_ ?_ ?_
    · show topAbCongr Ψ (abMk d0A) = Θ (abMk d0A)
      exact EquivLike.injective B.e (by rw [topAbCongr_abMk, hΨA, hΘA])
    · show topAbCongr Ψ (abMk d0S) = Θ (abMk d0S)
      exact EquivLike.injective B.e (by rw [topAbCongr_abMk, hΨS, hΘS])
    · show topAbCongr Ψ (abMk d0Y) = Θ (abMk d0Y)
      exact EquivLike.injective B.e (by rw [topAbCongr_abMk, hΨY, hΘY])
  -- the marked group isomorphism `e := Ψ⁻¹ ∘ equiv`; its abelianization is `eab`
  set e := orientBundle.equiv.trans Ψ.symm with he
  have hesymm : ∀ d : (D0 : Type), abMk (e.symm d) = eab (abMk d) := by
    intro d
    have h1 : e.symm d = orientBundle.equiv.symm (Ψ d) := rfl
    rw [h1, ← topAbCongr_symm_abMk]
    have h2 : (abMk (Ψ d) : topAbelianization (D0 : Type)) = topAbCongr Ψ (abMk d) := rfl
    rw [h2, hΨΘ (abMk d), hΘ]
    show (topAbCongr orientBundle.equiv).symm
      (topAbCongr orientBundle.equiv (eab (abMk d))) = eab (abMk d)
    rw [ContinuousMulEquiv.symm_apply_apply]
  refine ⟨e, ?_, ?_, ?_⟩
  · intro g hg
    rw [nu_ur_eq_nuUrBarAb_markedPi, markedPi_toAb, hg, hesymm d0A, eabA,
      ← nu_ur_eq_nuUrBarAb_markedPi, nu_ur_recip_unitNeg4]
  · intro g hg
    rw [nu_ur_eq_nuUrBarAb_markedPi, markedPi_toAb, hg, hesymm d0S, eabS, map_inv,
      ← nu_ur_eq_nuUrBarAb_markedPi, nu_ur_recip_uniformizer', ← ofAdd_neg]
    norm_num
  · intro g hg
    rw [nu_ur_eq_nuUrBarAb_markedPi, markedPi_toAb, hg, hesymm d0Y, eabY,
      ← nu_ur_eq_nuUrBarAb_markedPi, nu_ur_recip_unitNeg3]

end Assembly

end GQ2

/-! ### Paper-tag ledger (auto-generated by paperforge; do not edit)

  * Lemma 3.5 = ⟦lem-markedinitialform⟧
  * Proposition 1.1 = ⟦prop-markedDem⟧
  * Prop 3.8 = ⟦prop-orientationlift⟧ (= proposition 3.9 in current tex)
-/
