/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Opus-4.8 and Fable-5
-/
import GQ2.SectionThree
import GQ2.AppendixB
import GQ2.PeripheralAction
import GQ2.ZtwoPowering
import GQ2.FrattiniCriterion
import GQ2.FinitelyGenerated

/-!
# Construction of the anabelian bridge and lifting automorphisms

The topological-generation toolkit, presentation lifts, automorphisms, rows, and shear lifts.

See `GQ2.AnabelianBridge` for the paper-facing overview, source citations, and deviations.
-/

open scoped Classical

namespace GQ2

open Multiplicative

/-! ## `ẑ`-power helpers -/

section ZpowHatHelpers

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]

/-- `ẑ`-powers of inverses: `(x⁻¹) ^ᶻ γ = (x ^ᶻ γ)⁻¹`. -/
lemma zpowHat_inv (x : G) (γ : Zhat) : (x⁻¹) ^ᶻ γ = (x ^ᶻ γ)⁻¹ := by
  have hfun : (fun γ : Zhat => (x⁻¹) ^ᶻ γ) = fun γ : Zhat => (x ^ᶻ γ)⁻¹ := by
    refine Zhat.funext_ofInt (continuous_zpowHat _)
      (continuous_inv.comp (continuous_zpowHat _)) fun n => ?_
    rw [zpowHat_ofInt, zpowHat_ofInt, inv_zpow]
  exact congrFun hfun γ

/-- `ẑ`-powers commute with integer powers: `(x ^ᶻ γ) ^ n = (x ^ n) ^ᶻ γ`. -/
lemma zpowHat_zpow (x : G) (γ : Zhat) (n : ℤ) : (x ^ᶻ γ) ^ n = (x ^ n) ^ᶻ γ := by
  have hfun : (fun γ : Zhat => (x ^ᶻ γ) ^ n) = fun γ : Zhat => (x ^ n) ^ᶻ γ := by
    refine Zhat.funext_ofInt ((continuous_zpow n).comp (continuous_zpowHat _))
      (continuous_zpowHat _) fun m => ?_
    rw [zpowHat_ofInt, zpowHat_ofInt, ← zpow_mul, ← zpow_mul, mul_comm]
  exact congrFun hfun γ

omit [T2Space G] in
/-- `ẑ`-powers commute with conjugation: `(x ^ c) ^ᶻ γ = (x ^ᶻ γ) ^ c` (`conjP x c = c⁻¹xc`). -/
lemma zpowHat_conjP (x c : G) (γ : Zhat) : conjP x c ^ᶻ γ = conjP (x ^ᶻ γ) c := by
  set φ : ContinuousMonoidHom G G :=
    ⟨(MulAut.conj c⁻¹).toMonoidHom,
      ((continuous_const.mul continuous_id).mul continuous_const : Continuous
        fun g : G => c⁻¹ * g * (c⁻¹)⁻¹)⟩ with hφ
  have happ : ∀ g : G, φ g = conjP g c := fun g => by
    show (MulAut.conj c⁻¹) g = conjP g c
    rw [MulAut.conj_apply, conjP, inv_inv]
  rw [← happ, ← happ, map_zpowHat φ x γ]

end ZpowHatHelpers

/-! ## `ω₂` acts as the identity on pro-2 groups — the `hι_proj`/`hι_one` compatibility -/

section OmegaTwoProTwo

variable {P : Type} [Group P] [TopologicalSpace P] [IsTopologicalGroup P]
  [CompactSpace P] [T2Space P] [TotallyDisconnectedSpace P]

/-- On a pro-2 group, the profinite-exponentiation API idempotent `ω₂ ∈ ℤ̂` powers every element to itself:
`x ^ᶻ ω₂ = x`.  (`ω₂ ≡ 1` on the pro-2 part; every finite quotient of a pro-2 group is a
2-group, where `powOmega2` is the identity.) -/
theorem zpowHat_omega2_eq_self (hP : IsProP 2 P) (x : P) : x ^ᶻ omega2 = x := by
  have hmem : ∀ U : OpenNormalSubgroup P, (x ^ᶻ omega2) * x⁻¹ ∈ U := by
    intro U
    have : DiscreteTopology (P ⧸ U.toSubgroup) := by
      refine discreteTopology_of_isOpen_singleton_one ?_
      have hpre : (QuotientGroup.mk : P → P ⧸ U.toSubgroup) ⁻¹' {1}
          = (U.toSubgroup : Set P) := by
        ext δ
        simp only [Set.mem_preimage, Set.mem_singleton_iff, SetLike.mem_coe,
          QuotientGroup.eq_one_iff]
      rw [← (QuotientGroup.isQuotientMap_mk U.toSubgroup).isOpen_preimage, hpre]
      exact U.isOpen'
    have : Finite (P ⧸ U.toSubgroup) := Subgroup.quotient_finite_of_isOpen _ U.isOpen'
    have hω := map_zpowHat_omega2 (P := P ⧸ U.toSubgroup)
      { toMonoidHom := QuotientGroup.mk' U.toSubgroup
        continuous_toFun := continuous_quot_mk } x
    have hω' : QuotientGroup.mk' U.toSubgroup (x ^ᶻ omega2)
        = powOmega2 (QuotientGroup.mk' U.toSubgroup x) := hω
    obtain ⟨k, hk⟩ := (hP U) (QuotientGroup.mk' U.toSubgroup x)
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (orderOf_dvd_of_pow_eq_one hk)
    have hself : powOmega2 (QuotientGroup.mk' U.toSubgroup x)
        = QuotientGroup.mk' U.toSubgroup x := powOmega2_eq_self_of_orderOf_two_pow hj
    have hone : QuotientGroup.mk' U.toSubgroup ((x ^ᶻ omega2) * x⁻¹) = 1 := by
      rw [map_mul, map_inv, hω', hself, mul_inv_cancel]
    rwa [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hone
  have hprod := eq_one_of_forall_mem_openNormalSubgroup hmem
  rwa [mul_inv_eq_one] at hprod


/-- On a pro-2 group, B8's `ι`-powers are the 2-adic powers: `x ^ᶻ ι u = zpowZtwo x u`
(via the `hι_proj` pinning and the ℤ₂-powering development's `zpowHat_eq_zpowZtwo`). -/
theorem zpowHat_iota (R : PeripheralCyclotomicAction) (hP : IsProP 2 P) (x : P) (u : ℤ_[2]ˣ) :
    x ^ᶻ R.ι u = zpowZtwo hP x ((u : ℤ_[2])) := by
  rw [zpowHat_eq_zpowZtwo hP x (R.ι u), R.hι_proj u, toAdd_ofAdd]

end OmegaTwoProTwo

/-! ## Pinned topological generation -/

section PinnedGeneration

open CategoryTheory

/-- The free generators of a free profinite group **pinned-topologically-generate** it (the
generator-pinned refinement of `isTopologicallyFinGen_freeProfiniteGroup`; no finiteness of `X`
needed). -/
theorem freeProfiniteGroup_pinned_generation (X : Type) :
    (Subgroup.closure (Set.range (FreeProfiniteGroup.of (X := X)))).topologicalClosure = ⊤ := by
  set g : FreeGroup X →* FreeProfiniteGroup X :=
    (ProfiniteGrp.ProfiniteCompletion.eta (GrpCat.of (FreeGroup X))).hom with hg
  have hrange : Subgroup.closure (Set.range (FreeProfiniteGroup.of (X := X))) = g.range := by
    have h1 : Set.range (FreeProfiniteGroup.of (X := X))
        = ⇑g '' Set.range (FreeGroup.of : X → FreeGroup X) := by
      rw [← Set.range_comp]; rfl
    rw [h1, ← MonoidHom.map_closure, FreeGroup.closure_range_of X, ← MonoidHom.range_eq_map]
  rw [hrange]
  have hdense : DenseRange g := ProfiniteGrp.ProfiniteCompletion.denseRange _
  rw [SetLike.ext'_iff]
  simpa only [Subgroup.topologicalClosure_coe, Subgroup.coe_top, MonoidHom.coe_range]
    using hdense.closure_range

/-- Pinned topological generation pushes forward along a continuous surjection. -/
theorem pinned_generation_map {G Q : Type*}
    [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [Group Q] [TopologicalSpace Q] [IsTopologicalGroup Q]
    (f : G →* Q) (hf : Continuous f) (hfs : Function.Surjective f) {S : Set G}
    (hS : (Subgroup.closure S).topologicalClosure = ⊤) :
    (Subgroup.closure (⇑f '' S)).topologicalClosure = ⊤ := by
  rw [← MonoidHom.map_closure]
  exact hfs.denseRange.topologicalClosure_map_subgroup hf hS

/-- A continuous hom into a Hausdorff group vanishing on a pinned generating family's members
kills the whole closed generated subgroup. -/
theorem topClosure_closure_le_ker {G H : Type*}
    [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [Group H] [TopologicalSpace H] [T2Space H]
    (q : ContinuousMonoidHom G H) {S : Set G} (h : ∀ x ∈ S, q x = 1) :
    (Subgroup.closure S).topologicalClosure ≤ q.toMonoidHom.ker := by
  refine Subgroup.topologicalClosure_minimal _ ((Subgroup.closure_le _).mpr h) ?_
  have hker : (q.toMonoidHom.ker : Set G) = q ⁻¹' {1} := by
    ext x
    simp only [SetLike.mem_coe, MonoidHom.mem_ker, Set.mem_preimage, Set.mem_singleton_iff]
    rfl
  rw [hker]
  exact isClosed_singleton.preimage q.continuous_toFun

/-- A continuous hom sending a pinned generating family into a closed subgroup sends the whole
closed generated subgroup into it. -/
theorem topClosure_closure_le_comap {G H : Type*}
    [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [Group H] [TopologicalSpace H]
    (f : ContinuousMonoidHom G H) {S : Set G} {M : Subgroup H}
    (hM : IsClosed (M : Set H)) (h : ∀ x ∈ S, f x ∈ M) :
    (Subgroup.closure S).topologicalClosure ≤ M.comap f.toMonoidHom := by
  refine Subgroup.topologicalClosure_minimal _
    ((Subgroup.closure_le _).mpr fun x hx => Subgroup.mem_comap.mpr (h x hx)) ?_
  exact hM.preimage f.continuous_toFun

end PinnedGeneration

/-! ## `conjP` algebra -/

section ConjPAlgebra

variable {G : Type*} [Group G]

@[simp] private lemma conjP_mul (x y c : G) : conjP x c * conjP y c = conjP (x * y) c := by
  simp [conjP, mul_assoc]

@[simp] private lemma conjP_inv (x c : G) : (conjP x c)⁻¹ = conjP x⁻¹ c := by
  simp [conjP, mul_assoc]

@[simp] private lemma conjP_pow (x c : G) (n : ℕ) : conjP x c ^ n = conjP (x ^ n) c := by
  induction n with
  | zero => simp [conjP]
  | succ k ih => rw [pow_succ, pow_succ, ih, conjP_mul]

/-- The Demushkin relator in HNN form: `α²σ⁴[σ,ψ] = 1 ↔ ψ⁻¹σψ = σ⁻³α⁻²` (paper (16)). -/
lemma demushkin_relator_iff (α σ ψ : G) :
    α ^ 2 * σ ^ 4 * commP σ ψ = 1 ↔ conjP σ ψ = (σ ^ 3)⁻¹ * (α ^ 2)⁻¹ := by
  rw [commP, conjP]
  constructor
  · intro h
    have h' : α ^ 2 * σ ^ 3 * (ψ⁻¹ * σ * ψ) = 1 := by
      calc α ^ 2 * σ ^ 3 * (ψ⁻¹ * σ * ψ)
          = α ^ 2 * σ ^ 4 * (σ⁻¹ * ψ⁻¹ * σ * ψ) := by group
        _ = 1 := h
    calc ψ⁻¹ * σ * ψ = (α ^ 2 * σ ^ 3)⁻¹ * (α ^ 2 * σ ^ 3 * (ψ⁻¹ * σ * ψ)) := by group
      _ = (α ^ 2 * σ ^ 3)⁻¹ * 1 := by rw [h']
      _ = (σ ^ 3)⁻¹ * (α ^ 2)⁻¹ := by group
  · intro h
    calc α ^ 2 * σ ^ 4 * (σ⁻¹ * ψ⁻¹ * σ * ψ)
        = α ^ 2 * σ ^ 3 * (ψ⁻¹ * σ * ψ) := by group
      _ = α ^ 2 * σ ^ 3 * ((σ ^ 3)⁻¹ * (α ^ 2)⁻¹) := by rw [h]
      _ = 1 := by group

end ConjPAlgebra

/-! ## Presentation lifts: maps out of `Δ` and `D₀` into pro-2 targets -/

section Lifts

open CategoryTheory

variable {H : Type} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
  [CompactSpace H] [T2Space H] [TotallyDisconnectedSpace H]

/-- **Universal property of `Δ`** (free pro-2 on two generators): a pair of elements of a pro-2
group classifies a continuous hom `Δ → H`. -/
noncomputable def deltaLift (hH : IsProP 2 H) (m : Fin 2 → H) :
    ContinuousMonoidHom Delta H :=
  (maxProPHomEquiv hH).symm
    ((FreeProfiniteGroup.homEquiv (Fin 2) (ProfiniteGrp.of H)).symm m).hom

@[simp] private lemma deltaLift_P (hH : IsProP 2 H) (m : Fin 2 → H) :
    deltaLift hH m deltaP = m 0 := by
  show ((maxProPHomEquiv hH).symm _)
    (maxProPMk 2 (FreeProfiniteGroup (Fin 2)) (FreeProfiniteGroup.of 0)) = m 0
  rw [maxProPHomEquiv_symm_apply_maxProPMk]
  exact FreeProfiniteGroup.homEquiv_symm_of _ _ _

@[simp] private lemma deltaLift_T (hH : IsProP 2 H) (m : Fin 2 → H) :
    deltaLift hH m deltaT = m 1 := by
  show ((maxProPHomEquiv hH).symm _)
    (maxProPMk 2 (FreeProfiniteGroup (Fin 2)) (FreeProfiniteGroup.of 1)) = m 1
  rw [maxProPHomEquiv_symm_apply_maxProPMk]
  exact FreeProfiniteGroup.homEquiv_symm_of _ _ _

/-- **Universal property of `D₀`**: a triple of elements of a pro-2 group satisfying the
Demushkin relation classifies a continuous hom `D₀ → H`. -/
noncomputable def d0Lift (hH : IsProP 2 H) (m : Fin 3 → H)
    (hrel : m 0 ^ 2 * m 1 ^ 4 * commP (m 1) (m 2) = 1) :
    ContinuousMonoidHom D0 H :=
  (maxProPHomEquiv hH).symm
    (quotientLift (relatorSubgroup {d0Relator})
      ((FreeProfiniteGroup.homEquiv (Fin 3) (ProfiniteGrp.of H)).symm m).hom
      (by
        set f := ((FreeProfiniteGroup.homEquiv (Fin 3) (ProfiniteGrp.of H)).symm m).hom
        have hone : f.toMonoidHom d0Relator = 1 := by
          have h0 : f.toMonoidHom (FreeProfiniteGroup.of 0) = m 0 :=
            FreeProfiniteGroup.homEquiv_symm_of _ _ _
          have h1 : f.toMonoidHom (FreeProfiniteGroup.of 1) = m 1 :=
            FreeProfiniteGroup.homEquiv_symm_of _ _ _
          have h2 : f.toMonoidHom (FreeProfiniteGroup.of 2) = m 2 :=
            FreeProfiniteGroup.homEquiv_symm_of _ _ _
          simp only [d0Relator, map_mul, map_pow, Marking.map_commP, h0, h1, h2]
          exact hrel
        refine Subgroup.topologicalClosure_minimal _
          (Subgroup.normalClosure_le_normal ?_) ?_
        · intro r hr
          rwa [Set.mem_singleton_iff.mp hr, SetLike.mem_coe, MonoidHom.mem_ker]
        · have hker : (f.toMonoidHom.ker : Set (FreeProfiniteGroup (Fin 3)))
              = ⇑f ⁻¹' {1} := by
            ext x
            simp only [SetLike.mem_coe, MonoidHom.mem_ker, Set.mem_preimage,
              Set.mem_singleton_iff]
            rfl
          rw [hker]
          exact isClosed_singleton.preimage f.continuous_toFun))

@[simp] private lemma d0Lift_A (hH : IsProP 2 H) (m : Fin 3 → H)
    (hrel : m 0 ^ 2 * m 1 ^ 4 * commP (m 1) (m 2) = 1) :
    d0Lift hH m hrel d0A = m 0 := by
  show ((maxProPHomEquiv hH).symm _) (maxProPMk 2 D0Full
    (quotientMk (relatorSubgroup {d0Relator}) (FreeProfiniteGroup.of 0))) = m 0
  rw [maxProPHomEquiv_symm_apply_maxProPMk]
  exact (quotientLift_quotientMk _ _ _ _).trans (FreeProfiniteGroup.homEquiv_symm_of _ _ _)

@[simp] private lemma d0Lift_S (hH : IsProP 2 H) (m : Fin 3 → H)
    (hrel : m 0 ^ 2 * m 1 ^ 4 * commP (m 1) (m 2) = 1) :
    d0Lift hH m hrel d0S = m 1 := by
  show ((maxProPHomEquiv hH).symm _) (maxProPMk 2 D0Full
    (quotientMk (relatorSubgroup {d0Relator}) (FreeProfiniteGroup.of 1))) = m 1
  rw [maxProPHomEquiv_symm_apply_maxProPMk]
  exact (quotientLift_quotientMk _ _ _ _).trans (FreeProfiniteGroup.homEquiv_symm_of _ _ _)

@[simp] private lemma d0Lift_Y (hH : IsProP 2 H) (m : Fin 3 → H)
    (hrel : m 0 ^ 2 * m 1 ^ 4 * commP (m 1) (m 2) = 1) :
    d0Lift hH m hrel d0Y = m 2 := by
  show ((maxProPHomEquiv hH).symm _) (maxProPMk 2 D0Full
    (quotientMk (relatorSubgroup {d0Relator}) (FreeProfiniteGroup.of 2))) = m 2
  rw [maxProPHomEquiv_symm_apply_maxProPMk]
  exact (quotientLift_quotientMk _ _ _ _).trans (FreeProfiniteGroup.homEquiv_symm_of _ _ _)

end Lifts

/-! ## Pinned generation of `Δ` and `D₀`, and their topological finite generation -/

section PinnedInstances


/-- `D₀` is pro-2. -/
theorem isProP_d0 : IsProP 2 (D0 : Type) := isProP_maxProPQuotient

/-- `{P, T}` pinned-topologically-generate `Δ`. -/
theorem delta_pinned :
    (Subgroup.closure {deltaP, deltaT}).topologicalClosure = ⊤ := by
  have h := pinned_generation_map
    (maxProPMk 2 (FreeProfiniteGroup (Fin 2))).toMonoidHom
    (maxProPMk 2 (FreeProfiniteGroup (Fin 2))).continuous_toFun
    (quotientMk_surjective _)
    (freeProfiniteGroup_pinned_generation (Fin 2))
  have himg : (⇑(maxProPMk 2 (FreeProfiniteGroup (Fin 2))).toMonoidHom ''
      Set.range (FreeProfiniteGroup.of (X := Fin 2))) = {deltaP, deltaT} := by
    ext z
    constructor
    · rintro ⟨-, ⟨i, rfl⟩, rfl⟩
      fin_cases i
      · exact Set.mem_insert _ _
      · exact Set.mem_insert_of_mem _ rfl
    · rintro (rfl | rfl)
      · exact ⟨_, ⟨0, rfl⟩, rfl⟩
      · exact ⟨_, ⟨1, rfl⟩, rfl⟩
  rwa [himg] at h

/-- `{A, S, Y}` pinned-topologically-generate `D₀`. -/
theorem d0_pinned :
    (Subgroup.closure {d0A, d0S, d0Y}).topologicalClosure = ⊤ := by
  set π : FreeProfiniteGroup (Fin 3) →* (D0 : Type) :=
    (maxProPMk 2 D0Full).toMonoidHom.comp
      (quotientMk (relatorSubgroup {d0Relator})).toMonoidHom with hπ
  have hπc : Continuous π :=
    (maxProPMk 2 D0Full).continuous_toFun.comp
      (quotientMk (relatorSubgroup {d0Relator})).continuous_toFun
  have hπs : Function.Surjective π :=
    (quotientMk_surjective (proPKernel 2 D0Full)).comp
      (quotientMk_surjective (relatorSubgroup {d0Relator}))
  have h := pinned_generation_map π hπc hπs (freeProfiniteGroup_pinned_generation (Fin 3))
  have himg : (⇑π '' Set.range (FreeProfiniteGroup.of (X := Fin 3))) = {d0A, d0S, d0Y} := by
    ext z
    constructor
    · rintro ⟨-, ⟨i, rfl⟩, rfl⟩
      fin_cases i
      · exact Set.mem_insert _ _
      · exact Set.mem_insert_of_mem _ (Set.mem_insert _ _)
      · exact Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ rfl)
    · rintro (rfl | rfl | rfl)
      · exact ⟨_, ⟨0, rfl⟩, rfl⟩
      · exact ⟨_, ⟨1, rfl⟩, rfl⟩
      · exact ⟨_, ⟨2, rfl⟩, rfl⟩
  rwa [himg] at h

/-- `D₀` is topologically finitely generated (the `∃ s : Finset _` form `profinite_hopfian`
consumes). -/
theorem d0_topologicallyFinGen :
    ∃ s : Finset (D0 : Type), (Subgroup.closure (s : Set (D0 : Type))).topologicalClosure = ⊤ := by
  have hfin : ({d0A, d0S, d0Y} : Set (D0 : Type)).Finite :=
    (Set.finite_singleton _).insert _ |>.insert _
  refine ⟨hfin.toFinset, ?_⟩
  rw [Set.Finite.coe_toFinset]
  exact d0_pinned

end PinnedInstances

/-! ## The index-2 quotient toolkit -/

section IndexTwo

variable {K : Type} [Group K] [TopologicalSpace K] [IsTopologicalGroup K]
  [CompactSpace K] [T2Space K] [TotallyDisconnectedSpace K]

omit [CompactSpace K] [T2Space K] [TotallyDisconnectedSpace K] in
/-- Quotients by open normal subgroups are discrete. -/
lemma discreteTopology_quotient_openNormal (U : OpenNormalSubgroup K) :
    DiscreteTopology (K ⧸ U.toSubgroup) := by
  refine discreteTopology_of_isOpen_singleton_one ?_
  have hpre : (QuotientGroup.mk : K → K ⧸ U.toSubgroup) ⁻¹' {1}
      = (U.toSubgroup : Set K) := by
    ext δ
    simp only [Set.mem_preimage, Set.mem_singleton_iff, SetLike.mem_coe,
      QuotientGroup.eq_one_iff]
  rw [← (QuotientGroup.isQuotientMap_mk U.toSubgroup).isOpen_preimage, hpre]
  exact U.isOpen'

/-- Pro-2 powering fixes square-one elements: `x² = 1 ⇒ x^u = x` for `u ∈ ℤ₂ˣ` (odd exponents
act trivially on exponent-2 elements). -/
lemma zpowZtwo_eq_self_of_sq_eq_one {P : Type} [Group P] [TopologicalSpace P]
    [IsTopologicalGroup P] [CompactSpace P] [T2Space P] [TotallyDisconnectedSpace P]
    (hP : IsProP 2 P) {x : P} (hx : x ^ 2 = 1) (u : ℤ_[2]ˣ) :
    zpowZtwo hP x ((u : ℤ_[2])) = x := by
  obtain ⟨w, hw⟩ := two_dvd_val_sub_one u
  have hu : ((u : ℤ_[2])) = 1 + 2 * w := by rw [← hw]; ring
  rw [hu, zpowZtwo_add]
  have h2w : zpowZtwo hP x (2 * w) = 1 := by
    have hcomp := zpowZtwo_zpowZtwo hP x (2 : ℤ_[2]) w
    have h2 : zpowZtwo hP x ((2 : ℤ_[2])) = x ^ (2 : ℕ) := by
      have hcast : ((2 : ℤ_[2])) = (((2 : ℕ)) : ℤ_[2]) := by norm_num
      rw [hcast, zpowZtwo_natCast]
    rw [h2, hx, zpowZtwo_one_base] at hcomp
    exact hcomp.symm
  rw [h2w, mul_one, zpowZtwo_one_exp]

section AtIndexTwo

variable {M : OpenNormalSubgroup K} (hM : M.toSubgroup.index = 2)

include hM in
omit [T2Space K] [TotallyDisconnectedSpace K] in
/-- The index-2 quotient is commutative. -/
lemma quotient_mul_comm (z w : K ⧸ M.toSubgroup) : z * w = w * z := by
  have : Finite (K ⧸ M.toSubgroup) := Subgroup.quotient_finite_of_isOpen _ M.isOpen'
  have hcard : Nat.card (K ⧸ M.toSubgroup) = 2 := by
    rwa [← Subgroup.index_eq_card]
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have := isCyclic_of_prime_card (p := 2) hcard
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := K ⧸ M.toSubgroup)
  obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp (hg z)
  obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp (hg w)
  rw [← hi, ← hj, ← zpow_add, ← zpow_add, add_comm]

include hM in
omit [T2Space K] [TotallyDisconnectedSpace K] in
/-- Squares die in the index-2 quotient. -/
lemma quotient_sq_eq_one (z : K ⧸ M.toSubgroup) : z ^ 2 = 1 := by
  have : Finite (K ⧸ M.toSubgroup) := Subgroup.quotient_finite_of_isOpen _ M.isOpen'
  have hcard : Nat.card (K ⧸ M.toSubgroup) = 2 := by
    rwa [← Subgroup.index_eq_card]
  have hdvd : orderOf z ∣ 2 := hcard ▸ orderOf_dvd_natCard z
  exact orderOf_dvd_iff_pow_eq_one.mp hdvd

include hM in
omit [T2Space K] [TotallyDisconnectedSpace K] in
/-- Conjugation dies in the index-2 quotient. -/
lemma quotient_map_conjP (x c : K) :
    QuotientGroup.mk' M.toSubgroup (conjP x c) = QuotientGroup.mk' M.toSubgroup x := by
  rw [conjP, map_mul, map_mul, map_inv]
  calc (QuotientGroup.mk' M.toSubgroup c)⁻¹ * QuotientGroup.mk' M.toSubgroup x
        * QuotientGroup.mk' M.toSubgroup c
      = QuotientGroup.mk' M.toSubgroup x * (QuotientGroup.mk' M.toSubgroup c)⁻¹
        * QuotientGroup.mk' M.toSubgroup c := by
        rw [quotient_mul_comm hM ((QuotientGroup.mk' M.toSubgroup c)⁻¹)]
    _ = QuotientGroup.mk' M.toSubgroup x := by
        rw [mul_assoc, inv_mul_cancel, mul_one]

include hM in
omit [T2Space K] in
/-- **B8's `ι`-powers die in index-2 quotients**: `q(x ^ᶻ ι u) = q(x)` (`u` is odd). -/
lemma quotient_map_zpowHat_iota (R : PeripheralCyclotomicAction) (x : K) (u : ℤ_[2]ˣ) :
    QuotientGroup.mk' M.toSubgroup (x ^ᶻ R.ι u) = QuotientGroup.mk' M.toSubgroup x := by
  have := discreteTopology_quotient_openNormal M
  have : Finite (K ⧸ M.toSubgroup) := Subgroup.quotient_finite_of_isOpen _ M.isOpen'
  have h1 : IsTopologicalGroup (K ⧸ M.toSubgroup) := by infer_instance
  have h2 : CompactSpace (K ⧸ M.toSubgroup) := by infer_instance
  have h3 : TotallyDisconnectedSpace (K ⧸ M.toSubgroup) := by infer_instance
  have hnat := @map_zpowHat K _ _ _ _ _ (K ⧸ M.toSubgroup) _ _ h1 h2 h3
    ⟨QuotientGroup.mk' M.toSubgroup, continuous_quot_mk⟩ x (R.ι u)
  have hnat' : QuotientGroup.mk' M.toSubgroup (x ^ᶻ R.ι u)
      = (QuotientGroup.mk' M.toSubgroup x) ^ᶻ R.ι u := hnat
  have hpro : IsProP 2 (K ⧸ M.toSubgroup) := by
    refine isProP_of_isPGroup (IsPGroup.of_card (n := 1) ?_)
    rw [← Subgroup.index_eq_card, hM, pow_one]
  rw [hnat', zpowHat_iota R hpro,
    zpowZtwo_eq_self_of_sq_eq_one hpro (quotient_sq_eq_one hM _) u]

end AtIndexTwo

end IndexTwo

/-! ## The peripheral identity and its push to `D₀` -/

section Bridge

/-- **The combined B8 identity** (*): the three conjugation rows of Lemma 3.6 are tied together
by `φ_u` being a homomorphism and `P·T·C = 1`. -/
theorem peripheral_identity (R : PeripheralCyclotomicAction) (u : ℤ_[2]ˣ) :
    (conjP (deltaP ^ᶻ R.ι u) (R.cP u) * conjP (deltaT ^ᶻ R.ι u) (R.cT u))⁻¹
      = conjP ((deltaP * deltaT)⁻¹ ^ᶻ R.ι u) (R.cC u) := by
  rw [← R.hP u, ← R.hT u, ← map_mul, ← map_inv]
  exact R.hC u

/-- The transport hom `λ : Δ → D₀`, `P ↦ s³`, `T ↦ s⁻³a⁻²` (the paper's "view the words in
`E□ ⊆ D₀` via `P, T`" — the composite of its Tietze identifications, inlined). -/
noncomputable def lambdaHom : ContinuousMonoidHom (Delta : Type) (D0 : Type) :=
  deltaLift isProP_d0 ![d0S ^ 3, (d0S ^ 3)⁻¹ * (d0A ^ 2)⁻¹]

@[simp] private lemma lambdaHom_P : lambdaHom deltaP = d0S ^ 3 :=
  deltaLift_P _ _

@[simp] private lemma lambdaHom_T : lambdaHom deltaT = (d0S ^ 3)⁻¹ * (d0A ^ 2)⁻¹ :=
  deltaLift_T _ _

/-- The Demushkin relation in HNN form (paper (16)): `y⁻¹sy = s⁻³a⁻²` in `D₀`. -/
theorem d0_relation_hnn : conjP d0S d0Y = (d0S ^ 3)⁻¹ * (d0A ^ 2)⁻¹ :=
  (demushkin_relator_iff d0A d0S d0Y).mp d0_relation

/-- **The pushed identity**: transporting (*) along `λ` produces the conjugation identity that
the `Ψ_u`-relator check consumes. -/
theorem pushed_identity (R : PeripheralCyclotomicAction) (u : ℤ_[2]ˣ) :
    conjP (((d0S ^ 3)⁻¹ * (d0A ^ 2)⁻¹) ^ᶻ R.ι u) (lambdaHom (R.cT u))
      = conjP ((d0S ^ 3)⁻¹ ^ᶻ R.ι u) (lambdaHom (R.cP u))
        * conjP ((d0A ^ 2)⁻¹ ^ᶻ R.ι u) (lambdaHom (R.cC u)) := by
  have hconj : ∀ (x c : Delta), lambdaHom (conjP x c) = conjP (lambdaHom x) (lambdaHom c) := by
    intro x c
    simp [conjP, map_mul, map_inv]
  have hzpow : ∀ (x : Delta) (γ : Zhat), lambdaHom (x ^ᶻ γ) = (lambdaHom x) ^ᶻ γ :=
    fun x γ => map_zpowHat lambdaHom x γ
  have h := congrArg lambdaHom (peripheral_identity R u)
  simp only [hconj, hzpow, map_inv, map_mul, lambdaHom_P, lambdaHom_T] at h
  -- normalize the `C`-base: `λ((P·T)⁻¹) = a²`
  have hbase : ((d0S ^ 3 * ((d0S ^ 3)⁻¹ * (d0A ^ 2)⁻¹))⁻¹ : (D0 : Type)) = d0A ^ 2 := by
    group
  rw [hbase] at h
  -- h : (conjP (s³ ^ᶻιu) κP * conjP (τ ^ᶻιu) κT)⁻¹ = conjP (a² ^ᶻιu) κC; solve for the middle
  have hsolve : conjP (((d0S ^ 3)⁻¹ * (d0A ^ 2)⁻¹) ^ᶻ R.ι u) (lambdaHom (R.cT u))
      = (conjP ((d0S ^ 3) ^ᶻ R.ι u) (lambdaHom (R.cP u)))⁻¹
        * (conjP ((d0A ^ 2) ^ᶻ R.ι u) (lambdaHom (R.cC u)))⁻¹ := by
    have h' := congrArg (·⁻¹) h
    simp only [inv_inv] at h'
    -- h' : conjP (s³^ᶻιu) κP * conjP (τ^ᶻιu) κT = (conjP (a²^ᶻιu) κC)⁻¹
    calc conjP (((d0S ^ 3)⁻¹ * (d0A ^ 2)⁻¹) ^ᶻ R.ι u) (lambdaHom (R.cT u))
        = (conjP ((d0S ^ 3) ^ᶻ R.ι u) (lambdaHom (R.cP u)))⁻¹
          * (conjP ((d0S ^ 3) ^ᶻ R.ι u) (lambdaHom (R.cP u))
            * conjP (((d0S ^ 3)⁻¹ * (d0A ^ 2)⁻¹) ^ᶻ R.ι u) (lambdaHom (R.cT u))) := by
          group
      _ = (conjP ((d0S ^ 3) ^ᶻ R.ι u) (lambdaHom (R.cP u)))⁻¹
          * (conjP ((d0A ^ 2) ^ᶻ R.ι u) (lambdaHom (R.cC u)))⁻¹ := by rw [h']
  rw [hsolve, conjP_inv, conjP_inv, zpowHat_inv, zpowHat_inv]

end Bridge

/-! ## `Ψ_u` : construction, surjectivity, automorphism -/

section Psi

/-- `ẑ`-powers commute with natural-number powers. -/
lemma zpowHat_pow {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
    (x : G) (γ : Zhat) (n : ℕ) : (x ^ᶻ γ) ^ n = (x ^ n) ^ᶻ γ := by
  have h := zpowHat_zpow x γ (n : ℤ)
  rwa [zpow_natCast, zpow_natCast] at h

variable (R : PeripheralCyclotomicAction) (u : ℤ_[2]ˣ)

/-- The `Ψ_u`-marking respects the Demushkin relator (via the HNN form (16) and the pushed
peripheral identity). -/
lemma psi_relator :
    (conjP (d0A ^ᶻ R.ι u) (lambdaHom (R.cC u))) ^ 2
      * (conjP (d0S ^ᶻ R.ι u) (lambdaHom (R.cP u))) ^ 4
      * commP (conjP (d0S ^ᶻ R.ι u) (lambdaHom (R.cP u)))
          ((lambdaHom (R.cP u))⁻¹ * d0Y * lambdaHom (R.cT u)) = 1 := by
  refine (demushkin_relator_iff _ _ _).mpr ?_
  have hL : conjP (conjP (d0S ^ᶻ R.ι u) (lambdaHom (R.cP u)))
      ((lambdaHom (R.cP u))⁻¹ * d0Y * lambdaHom (R.cT u))
      = conjP ((conjP d0S d0Y) ^ᶻ R.ι u) (lambdaHom (R.cT u)) := by
    rw [zpowHat_conjP]
    simp only [conjP]
    group
  have hm1 : (conjP (d0S ^ᶻ R.ι u) (lambdaHom (R.cP u))) ^ 3
      = conjP ((d0S ^ 3) ^ᶻ R.ι u) (lambdaHom (R.cP u)) := by
    rw [conjP_pow, zpowHat_pow]
  have hm0 : (conjP (d0A ^ᶻ R.ι u) (lambdaHom (R.cC u))) ^ 2
      = conjP ((d0A ^ 2) ^ᶻ R.ι u) (lambdaHom (R.cC u)) := by
    rw [conjP_pow, zpowHat_pow]
  calc conjP (conjP (d0S ^ᶻ R.ι u) (lambdaHom (R.cP u)))
        ((lambdaHom (R.cP u))⁻¹ * d0Y * lambdaHom (R.cT u))
      = conjP ((conjP d0S d0Y) ^ᶻ R.ι u) (lambdaHom (R.cT u)) := hL
    _ = conjP (((d0S ^ 3)⁻¹ * (d0A ^ 2)⁻¹) ^ᶻ R.ι u) (lambdaHom (R.cT u)) := by
        rw [d0_relation_hnn]
    _ = conjP ((d0S ^ 3)⁻¹ ^ᶻ R.ι u) (lambdaHom (R.cP u))
        * conjP ((d0A ^ 2)⁻¹ ^ᶻ R.ι u) (lambdaHom (R.cC u)) := pushed_identity R u
    _ = ((conjP (d0S ^ᶻ R.ι u) (lambdaHom (R.cP u))) ^ 3)⁻¹
        * ((conjP (d0A ^ᶻ R.ι u) (lambdaHom (R.cC u))) ^ 2)⁻¹ := by
        rw [hm1, hm0, conjP_inv, conjP_inv, zpowHat_inv, zpowHat_inv]

/-- **`Ψ_u`** as a continuous endomorphism of `D₀`: `A ↦ (A^u)^{κ_C}`, `S ↦ (S^u)^{κ_P}`,
`Y ↦ κ_P⁻¹ Y κ_T` (paper, proof of Lemma 3.7). -/
noncomputable def psiHom : ContinuousMonoidHom (D0 : Type) (D0 : Type) :=
  d0Lift isProP_d0
    ![conjP (d0A ^ᶻ R.ι u) (lambdaHom (R.cC u)),
      conjP (d0S ^ᶻ R.ι u) (lambdaHom (R.cP u)),
      (lambdaHom (R.cP u))⁻¹ * d0Y * lambdaHom (R.cT u)]
    (psi_relator R u)

@[simp] private lemma psiHom_A : psiHom R u d0A = conjP (d0A ^ᶻ R.ι u) (lambdaHom (R.cC u)) :=
  d0Lift_A _ _ _

@[simp] private lemma psiHom_S : psiHom R u d0S = conjP (d0S ^ᶻ R.ι u) (lambdaHom (R.cP u)) :=
  d0Lift_S _ _ _

@[simp] private lemma psiHom_Y :
    psiHom R u d0Y = (lambdaHom (R.cP u))⁻¹ * d0Y * lambdaHom (R.cT u) :=
  d0Lift_Y _ _ _

/-- `λ` lands in the closed subgroup generated by `s, a`. -/
lemma lambdaHom_mem_closure (γ : Delta) :
    lambdaHom γ ∈ (Subgroup.closure {d0S, d0A}).topologicalClosure := by
  have hcl : IsClosed (((Subgroup.closure {d0S, d0A}).topologicalClosure : Subgroup (D0 : Type))
      : Set (D0 : Type)) := Subgroup.isClosed_topologicalClosure _
  have hS : d0S ∈ (Subgroup.closure {d0S, d0A}).topologicalClosure :=
    Subgroup.le_topologicalClosure _ (Subgroup.subset_closure (Set.mem_insert _ _))
  have hA : d0A ∈ (Subgroup.closure {d0S, d0A}).topologicalClosure :=
    Subgroup.le_topologicalClosure _
      (Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl))
  have hle := topClosure_closure_le_comap lambdaHom (S := {deltaP, deltaT}) hcl ?_
  · have hmem :
        γ ∈ (Subgroup.closure ({deltaP, deltaT} : Set (Delta : Type))).topologicalClosure := by
      rw [delta_pinned]
      exact Subgroup.mem_top γ
    exact Subgroup.mem_comap.mp (hle hmem)
  · rintro x (rfl | rfl)
    · rw [lambdaHom_P]
      exact pow_mem hS 3
    · rw [lambdaHom_T]
      exact mul_mem (inv_mem (pow_mem hS 3)) (inv_mem (pow_mem hA 2))

/-- **`Ψ_u` is surjective** (the pro-2 Frattini criterion: in every index-2 quotient the
`u`-powers and the conjugators are invisible, so `Ψ_u` moves the generators by elements the
generators already reach). -/
theorem psiHom_surjective : Function.Surjective (psiHom R u) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine surjective_of_forall_index_p_quotient_surjective isProP_d0 (psiHom R u) ?_
  intro M hM
  have := discreteTopology_quotient_openNormal M
  have : Finite ((D0 : Type) ⧸ M.toSubgroup) := Subgroup.quotient_finite_of_isOpen _ M.isOpen'
  have hcard : Nat.card ((D0 : Type) ⧸ M.toSubgroup) = 2 := by
    rwa [← Subgroup.index_eq_card]
  have : Fact (Nat.Prime (Nat.card ((D0 : Type) ⧸ M.toSubgroup))) := ⟨hcard ▸ Nat.prime_two⟩
  set c : (D0 : Type) →* ((D0 : Type) ⧸ M.toSubgroup) :=
    (QuotientGroup.mk' M.toSubgroup).comp (psiHom R u).toMonoidHom with hcdef
  rcases c.range.eq_bot_or_eq_top_of_prime_card with hbot | htop
  · -- the trivial-range case is absurd: it forces the whole quotient to be trivial
    exfalso
    have hval : ∀ g : (D0 : Type), QuotientGroup.mk' M.toSubgroup (psiHom R u g) = 1 := by
      intro g
      have hmem : c g ∈ c.range := ⟨g, rfl⟩
      rw [hbot] at hmem
      exact Subgroup.mem_bot.mp hmem
    -- the quotient map kills `a` and `s` …
    have hqa : QuotientGroup.mk' M.toSubgroup d0A = 1 := by
      have h := hval d0A
      rwa [psiHom_A, quotient_map_conjP hM, quotient_map_zpowHat_iota hM R] at h
    have hqs : QuotientGroup.mk' M.toSubgroup d0S = 1 := by
      have h := hval d0S
      rwa [psiHom_S, quotient_map_conjP hM, quotient_map_zpowHat_iota hM R] at h
    -- … hence the conjugators (which lie in `⟨s,a⟩`-closure) …
    have hkerSA := topClosure_closure_le_ker
      (⟨QuotientGroup.mk' M.toSubgroup, continuous_quot_mk⟩ :
        ContinuousMonoidHom (D0 : Type) ((D0 : Type) ⧸ M.toSubgroup))
      (S := {d0S, d0A}) (by rintro x (rfl | rfl) <;> assumption)
    have hκ : ∀ γ : Delta, QuotientGroup.mk' M.toSubgroup (lambdaHom γ) = 1 := fun γ =>
      MonoidHom.mem_ker.mp (hkerSA (lambdaHom_mem_closure γ))
    -- … hence `y` …
    have hqy : QuotientGroup.mk' M.toSubgroup d0Y = 1 := by
      have h := hval d0Y
      rwa [psiHom_Y, map_mul, map_mul, map_inv, hκ (R.cP u), hκ (R.cT u), inv_one, one_mul,
        mul_one] at h
    -- … hence everything: the quotient is trivial, contradicting index 2.
    have hkerAll := topClosure_closure_le_ker
      (⟨QuotientGroup.mk' M.toSubgroup, continuous_quot_mk⟩ :
        ContinuousMonoidHom (D0 : Type) ((D0 : Type) ⧸ M.toSubgroup))
      (S := {d0A, d0S, d0Y}) (by rintro x (rfl | rfl | rfl) <;> assumption)
    have : Nontrivial ((D0 : Type) ⧸ M.toSubgroup) := by
      rw [← Finite.one_lt_card_iff_nontrivial, hcard]
      norm_num
    obtain ⟨z, hz⟩ := exists_ne (1 : (D0 : Type) ⧸ M.toSubgroup)
    obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective M.toSubgroup z
    refine hz (MonoidHom.mem_ker.mp (hkerAll ?_))
    rw [d0_pinned]
    exact Subgroup.mem_top g
  · -- full range: the composite is surjective
    intro z
    have hmem : z ∈ c.range := htop ▸ Subgroup.mem_top z
    exact hmem

/-- **`Ψ_u` is a continuous automorphism of `D₀`** (surjectivity + Hopficity). -/
noncomputable def psiEquiv : ContinuousMulEquiv (D0 : Type) (D0 : Type) :=
  continuousMulEquivOfBijective (psiHom R u)
    ⟨profinite_hopfian d0_topologicallyFinGen (psiHom R u) (psiHom_surjective R u),
      psiHom_surjective R u⟩

@[simp] private lemma psiEquiv_apply (x : (D0 : Type)) : psiEquiv R u x = psiHom R u x := rfl

end Psi

/-! ## The abelianized rows (paper (15)) and Lemma 3.7 -/

section Rows

open SectionThree

/-- 2-adic powering on `Multiplicative ℤ₂` is multiplication of exponents. -/
lemma zpowZtwo_multPadicInt (c u : ℤ_[2]) :
    zpowZtwo PropOneOne.isProP_two_multPadicInt (ofAdd c) u = ofAdd (c * u) := by
  have hcont : Continuous fun w : Multiplicative ℤ_[2] => ofAdd (c * w.toAdd) :=
    continuous_ofAdd.comp ((continuous_const_mul c).comp continuous_toAdd)
  have h := zpowZtwoHom_unique PropOneOne.isProP_two_multPadicInt
    (φ := AddMonoidHom.toMultiplicative (AddMonoidHom.mulLeft c)) hcont u
  have hl : (AddMonoidHom.toMultiplicative (AddMonoidHom.mulLeft c)) (ofAdd u)
      = ofAdd (c * u) := rfl
  have hone : (AddMonoidHom.toMultiplicative (AddMonoidHom.mulLeft c)) (ofAdd 1)
      = ofAdd (c * 1) := rfl
  rw [hl, hone, mul_one] at h
  exact h.symm

/-- The coordinate group of eq. (11). -/
local notation "Bcoord" => Multiplicative (ZMod 2 × ℤ_[2] × ℤ_[2])

/-- `ι u`-powering on the coordinate group acts trivially on the `ℤ/2`-component and by
`u`-multiplication on the `ℤ₂`-components. -/
lemma zpowHat_iota_multProd (R : PeripheralCyclotomicAction) (u : ℤ_[2]ˣ)
    (c₀ : ZMod 2) (c₁ c₂ : ℤ_[2]) :
    (ofAdd ((c₀, c₁, c₂) : ZMod 2 × ℤ_[2] × ℤ_[2]) : Bcoord) ^ᶻ R.ι u
      = ofAdd ((c₀, (u : ℤ_[2]) * c₁, (u : ℤ_[2]) * c₂)) := by
  -- the three coordinate projections, as continuous homs
  set π₁ : ContinuousMonoidHom Bcoord (Multiplicative (ZMod 2)) :=
    ⟨AddMonoidHom.toMultiplicative (AddMonoidHom.fst (ZMod 2) (ℤ_[2] × ℤ_[2])),
      continuous_ofAdd.comp (continuous_fst.comp continuous_toAdd)⟩ with hπ₁
  set π₂ : ContinuousMonoidHom Bcoord (Multiplicative ℤ_[2]) :=
    ⟨AddMonoidHom.toMultiplicative
        ((AddMonoidHom.fst ℤ_[2] ℤ_[2]).comp (AddMonoidHom.snd (ZMod 2) (ℤ_[2] × ℤ_[2]))),
      continuous_ofAdd.comp ((continuous_fst.comp continuous_snd).comp continuous_toAdd)⟩ with hπ₂
  set π₃ : ContinuousMonoidHom Bcoord (Multiplicative ℤ_[2]) :=
    ⟨AddMonoidHom.toMultiplicative
        ((AddMonoidHom.snd ℤ_[2] ℤ_[2]).comp (AddMonoidHom.snd (ZMod 2) (ℤ_[2] × ℤ_[2]))),
      continuous_ofAdd.comp ((continuous_snd.comp continuous_snd).comp continuous_toAdd)⟩ with hπ₃
  -- component 1: exponent 2, so `ι u` acts trivially
  have h₁ : π₁ ((ofAdd ((c₀, c₁, c₂) : ZMod 2 × ℤ_[2] × ℤ_[2]) : Bcoord) ^ᶻ R.ι u)
      = ofAdd c₀ := by
    rw [map_zpowHat π₁]
    have hbase : π₁ (ofAdd ((c₀, c₁, c₂) : ZMod 2 × ℤ_[2] × ℤ_[2])) = ofAdd c₀ := rfl
    rw [hbase]
    have hpro : IsProP 2 (Multiplicative (ZMod 2)) := by
      refine isProP_of_isPGroup (IsPGroup.of_card (n := 1) ?_)
      simp [Nat.card_eq_fintype_card]
    have hsq : (ofAdd c₀ : Multiplicative (ZMod 2)) ^ 2 = 1 := by
      rw [pow_two, ← ofAdd_add, CharTwo.add_self_eq_zero]
      rfl
    rw [zpowHat_iota R hpro, zpowZtwo_eq_self_of_sq_eq_one hpro hsq u]
  -- components 2, 3: `u`-multiplication
  have h₂ : π₂ ((ofAdd ((c₀, c₁, c₂) : ZMod 2 × ℤ_[2] × ℤ_[2]) : Bcoord) ^ᶻ R.ι u)
      = ofAdd (c₁ * (u : ℤ_[2])) := by
    rw [map_zpowHat π₂]
    have hbase : π₂ (ofAdd ((c₀, c₁, c₂) : ZMod 2 × ℤ_[2] × ℤ_[2])) = ofAdd c₁ := rfl
    rw [hbase, zpowHat_iota R PropOneOne.isProP_two_multPadicInt,
      zpowZtwo_multPadicInt]
  have h₃ : π₃ ((ofAdd ((c₀, c₁, c₂) : ZMod 2 × ℤ_[2] × ℤ_[2]) : Bcoord) ^ᶻ R.ι u)
      = ofAdd (c₂ * (u : ℤ_[2])) := by
    rw [map_zpowHat π₃]
    have hbase : π₃ (ofAdd ((c₀, c₁, c₂) : ZMod 2 × ℤ_[2] × ℤ_[2])) = ofAdd c₂ := rfl
    rw [hbase, zpowHat_iota R PropOneOne.isProP_two_multPadicInt,
      zpowZtwo_multPadicInt]
  -- reassemble from components
  have hext : ∀ z w : Bcoord, π₁ z = π₁ w → π₂ z = π₂ w → π₃ z = π₃ w → z = w := by
    intro z w e₁ e₂ e₃
    have t₁ : z.toAdd.1 = w.toAdd.1 := congrArg Multiplicative.toAdd e₁
    have t₂ : z.toAdd.2.1 = w.toAdd.2.1 := congrArg Multiplicative.toAdd e₂
    have t₃ : z.toAdd.2.2 = w.toAdd.2.2 := congrArg Multiplicative.toAdd e₃
    have : z.toAdd = w.toAdd := Prod.ext t₁ (Prod.ext t₂ t₃)
    exact Multiplicative.toAdd.injective this
  refine hext _ _ ?_ ?_ ?_
  · rw [h₁]; rfl
  · rw [h₂]
    show ofAdd (c₁ * (u : ℤ_[2])) = ofAdd ((u : ℤ_[2]) * c₁)
    rw [mul_comm]
  · rw [h₃]
    show ofAdd (c₂ * (u : ℤ_[2])) = ofAdd ((u : ℤ_[2]) * c₂)
    rw [mul_comm]

variable (B : SectionThree.BDecomposition)

/-- The coordinate hom `φ = B.e ∘ abMk : D₀ → ℤ/2 × ℤ₂ × ℤ₂` of eq. (11). -/
noncomputable def bCoordHom : ContinuousMonoidHom (D0 : Type) Bcoord :=
  ⟨B.e.toMulEquiv.toMonoidHom.comp (abMk (G := (D0 : Type))),
    B.e.continuous_toFun.comp continuous_abMk⟩

private lemma bCoordHom_apply (x : (D0 : Type)) : bCoordHom B x = B.e (abMk x) := rfl

private lemma bCoordHom_conjP (x c : (D0 : Type)) : bCoordHom B (conjP x c) = bCoordHom B x := by
  rw [conjP, map_mul, map_mul, map_inv, mul_comm ((bCoordHom B c)⁻¹) (bCoordHom B x),
    mul_assoc, inv_mul_cancel, mul_one]

private lemma bCoordHom_S : bCoordHom B d0S = ofAdd ((0 : ZMod 2), (1 : ℤ_[2]), (0 : ℤ_[2])) :=
  B.map_S

private lemma bCoordHom_A : bCoordHom B d0A = ofAdd ((1 : ZMod 2), (-2 : ℤ_[2]), (0 : ℤ_[2])) := by
  have hsplit : d0A = (d0A * d0S ^ 2) * (d0S ^ 2)⁻¹ := by group
  have hφt : bCoordHom B (d0A * d0S ^ 2)
      = ofAdd ((1 : ZMod 2), (0 : ℤ_[2]), (0 : ℤ_[2])) := B.map_t
  rw [hsplit, map_mul, map_inv, map_pow, hφt, bCoordHom_S, ← ofAdd_nsmul, ← ofAdd_neg,
    ← ofAdd_add]
  congr 1
  simp

/-- The `Ā`-row of `Ψ_u` (paper (15)): `Ā = (1,−2,0) ↦ (1,−2u,0)`. -/
lemma bCoord_psiHom_A (R : PeripheralCyclotomicAction) (u : ℤ_[2]ˣ) :
    bCoordHom B (psiHom R u d0A) = ofAdd ((1 : ZMod 2), -2 * (u : ℤ_[2]), (0 : ℤ_[2])) := by
  rw [psiHom_A, bCoordHom_conjP, map_zpowHat (bCoordHom B), bCoordHom_A, zpowHat_iota_multProd]
  congr 1
  simp only [Prod.mk.injEq]
  exact ⟨trivial, by ring, by ring⟩

/-- The `S̄`-row of `Ψ_u` (paper (15)): `S̄ = (0,1,0) ↦ (0,u,0)`. -/
lemma bCoord_psiHom_S (R : PeripheralCyclotomicAction) (u : ℤ_[2]ˣ) :
    bCoordHom B (psiHom R u d0S) = ofAdd ((0 : ZMod 2), (u : ℤ_[2]), (0 : ℤ_[2])) := by
  rw [psiHom_S, bCoordHom_conjP, map_zpowHat (bCoordHom B), bCoordHom_S, zpowHat_iota_multProd]
  congr 1
  simp only [Prod.mk.injEq]
  exact ⟨trivial, by ring, by ring⟩

namespace SectionThree

/-- **Lemma 3.7** (paper (15)): for every `u ∈ ℤ₂ˣ` there is a continuous automorphism `Ψ_u`
of `D₀` acting on `B`-coordinates by `Ā = (1,−2,0) ↦ (1,−2u,0)`, `S̄ = (0,1,0) ↦ (0,u,0)`.
Consumes axiom **B8** (`peripheralCyclotomicAction`).  Declared here (not in
`GQ2/SectionThree.lean`) because the proof needs this file's bridge; same namespace, per the
Prop. 3.2 precedent (`GQ2/Prop32.lean`). -/
theorem lemma_3_7 (u : ℤ_[2]ˣ) :
    ∃ Ψ : ContinuousMulEquiv (D0 : Type) (D0 : Type),
      B.e (abMk (Ψ d0A)) = Multiplicative.ofAdd (1, -2 * (u : ℤ_[2]), 0) ∧
      B.e (abMk (Ψ d0S)) = Multiplicative.ofAdd (0, (u : ℤ_[2]), 0) :=
  ⟨psiEquiv peripheralCyclotomicAction u,
    (bCoordHom_apply B _).symm.trans (bCoord_psiHom_A B _ u),
    (bCoordHom_apply B _).symm.trans (bCoord_psiHom_S B _ u)⟩

end SectionThree

end Rows

/-! ## Proposition 3.8, lifting half: the shear `Θ_b` (paper (19)) and the composite -/

section Shear

open SectionThree

/-- `S^b` for a 2-adic exponent `b`. -/
noncomputable def sPow (b : ℤ_[2]) : (D0 : Type) := zpowZtwo isProP_d0 d0S b

private lemma sPow_mul_neg (b : ℤ_[2]) : sPow b * sPow (-b) = 1 := by
  rw [sPow, sPow, ← zpowZtwo_add, add_neg_cancel, SectionThree.zpowZtwo_zero]

/-- Ordinary `S`-powers commute with `S^b`. -/
lemma commute_pow_sPow (n : ℕ) (b : ℤ_[2]) : Commute (d0S ^ n) (sPow b) := by
  have h1 : d0S ^ n = zpowZtwo isProP_d0 d0S ((n : ℕ) : ℤ_[2]) := (zpowZtwo_natCast _ _ _).symm
  show d0S ^ n * sPow b = sPow b * d0S ^ n
  rw [h1, sPow, ← zpowZtwo_add, ← zpowZtwo_add, add_comm]

private lemma conjP_pow_sPow (n : ℕ) (b : ℤ_[2]) : conjP (d0S ^ n) (sPow b) = d0S ^ n := by
  rw [conjP, mul_assoc, (commute_pow_sPow n b).eq, ← mul_assoc, inv_mul_cancel, one_mul]

/-- Composing conjugations multiplies the conjugators. -/
lemma conjP_conjP {G : Type*} [Group G] (x c d : G) :
    conjP (conjP x c) d = conjP x (c * d) := by
  simp only [conjP]
  group

@[simp] private lemma conjP_one {G : Type*} [Group G] (x : G) : conjP x 1 = x := by
  simp [conjP]

/-- The shear marking respects the Demushkin relator (paper (19)):
`Θ_b(A) = A^{S^b}`, `Θ_b(S) = S`, `Θ_b(Y) = Y·S^b`. -/
lemma theta_relator (b : ℤ_[2]) :
    (conjP d0A (sPow b)) ^ 2 * d0S ^ 4 * commP d0S (d0Y * sPow b) = 1 := by
  refine (demushkin_relator_iff _ _ _).mpr ?_
  have hL : conjP d0S (d0Y * sPow b) = conjP (conjP d0S d0Y) (sPow b) := by
    simp only [conjP]
    group
  rw [hL, d0_relation_hnn]
  calc conjP ((d0S ^ 3)⁻¹ * (d0A ^ 2)⁻¹) (sPow b)
      = conjP ((d0S ^ 3)⁻¹) (sPow b) * conjP ((d0A ^ 2)⁻¹) (sPow b) :=
        (conjP_mul _ _ _).symm
    _ = (conjP (d0S ^ 3) (sPow b))⁻¹ * (conjP (d0A ^ 2) (sPow b))⁻¹ := by
        rw [← conjP_inv, ← conjP_inv]
    _ = (d0S ^ 3)⁻¹ * ((conjP d0A (sPow b)) ^ 2)⁻¹ := by
        rw [conjP_pow_sPow, conjP_pow]

/-- **The shear `Θ_b`** (paper (19)) as a continuous endomorphism of `D₀`. -/
noncomputable def thetaHom (b : ℤ_[2]) : ContinuousMonoidHom (D0 : Type) (D0 : Type) :=
  d0Lift isProP_d0 ![conjP d0A (sPow b), d0S, d0Y * sPow b] (theta_relator b)

@[simp] private lemma thetaHom_A (b : ℤ_[2]) : thetaHom b d0A = conjP d0A (sPow b) := d0Lift_A _ _ _
@[simp] private lemma thetaHom_S (b : ℤ_[2]) : thetaHom b d0S = d0S := d0Lift_S _ _ _
@[simp] private lemma thetaHom_Y (b : ℤ_[2]) : thetaHom b d0Y = d0Y * sPow b := d0Lift_Y _ _ _

/-- Extensionality on `D₀`: continuous homs agreeing on the three marked generators agree. -/
lemma d0Hom_ext {H : Type*} [Group H] [TopologicalSpace H] [T2Space H]
    {f g : ContinuousMonoidHom (D0 : Type) H}
    (hA : f d0A = g d0A) (hS : f d0S = g d0S) (hY : f d0Y = g d0Y) : f = g := by
  set E : Subgroup (D0 : Type) :=
    { carrier := {x | f x = g x}
      one_mem' := by simp only [Set.mem_setOf_eq, map_one]
      mul_mem' := fun ha hb => by
        simp only [Set.mem_setOf_eq] at *
        rw [map_mul, map_mul, ha, hb]
      inv_mem' := fun ha => by
        simp only [Set.mem_setOf_eq] at *
        rw [map_inv, map_inv, ha] } with hE
  have hle : (Subgroup.closure {d0A, d0S, d0Y}).topologicalClosure ≤ E := by
    refine Subgroup.topologicalClosure_minimal _ ((Subgroup.closure_le _).mpr ?_) ?_
    · rintro x (rfl | rfl | rfl) <;> assumption
    · exact isClosed_eq f.continuous_toFun g.continuous_toFun
  refine DFunLike.ext _ _ fun x => ?_
  exact hle (by rw [d0_pinned]; exact Subgroup.mem_top x)

/-- `Θ_b` fixes every `S`-power. -/
lemma thetaHom_sPow (b c : ℤ_[2]) : thetaHom b (sPow c) = sPow c := by
  rw [sPow, map_zpowZtwo isProP_d0 isProP_d0 (thetaHom b) d0S c, thetaHom_S]

/-- `Θ_b ∘ Θ_{−b} = id` on points. -/
lemma thetaHom_comp_neg (b : ℤ_[2]) (x : (D0 : Type)) : thetaHom b (thetaHom (-b) x) = x := by
  have hext : (thetaHom b).comp (thetaHom (-b))
      = (⟨MonoidHom.id _, continuous_id⟩ : ContinuousMonoidHom (D0 : Type) (D0 : Type)) := by
    refine d0Hom_ext ?_ ?_ ?_
    · show thetaHom b (thetaHom (-b) d0A) = d0A
      rw [thetaHom_A]
      have hpush : thetaHom b (conjP d0A (sPow (-b)))
          = conjP (thetaHom b d0A) (thetaHom b (sPow (-b))) := by
        simp only [conjP, map_mul, map_inv]
      rw [hpush, thetaHom_A, thetaHom_sPow, conjP_conjP, sPow_mul_neg, conjP_one]
    · show thetaHom b (thetaHom (-b) d0S) = d0S
      rw [thetaHom_S, thetaHom_S]
    · show thetaHom b (thetaHom (-b) d0Y) = d0Y
      rw [thetaHom_Y, map_mul, thetaHom_Y, thetaHom_sPow, mul_assoc, sPow_mul_neg, mul_one]
  exact DFunLike.congr_fun hext x

/-- **`Θ_b` is a continuous automorphism** (inverse `Θ_{−b}`). -/
noncomputable def thetaEquiv (b : ℤ_[2]) : ContinuousMulEquiv (D0 : Type) (D0 : Type) :=
  continuousMulEquivOfBijective (thetaHom b)
    (Function.bijective_iff_has_inverse.mpr
      ⟨thetaHom (-b),
        fun x => by
          have h := thetaHom_comp_neg (-b) x
          rwa [neg_neg] at h,
        fun x => thetaHom_comp_neg b x⟩)

@[simp] private lemma thetaEquiv_apply (b : ℤ_[2]) (x : (D0 : Type)) :
    thetaEquiv b x = thetaHom b x := rfl

end Shear

/-! ## The `Ȳ`-row of `Ψ_u`, and Proposition 3.8 (lifting half) -/

section LiftHalf

open SectionThree

variable (B : SectionThree.BDecomposition)

/-- The coordinate subgroup `{(0, ∗, 0)}`-shaped constraint: trivial `ℤ/2`- and
`Ȳ`-components. -/
noncomputable def bcoordMiddle : Subgroup (Multiplicative (ZMod 2 × ℤ_[2] × ℤ_[2])) where
  carrier := {z | z.toAdd.1 = 0 ∧ z.toAdd.2.2 = 0}
  one_mem' := ⟨rfl, rfl⟩
  mul_mem' := by
    rintro a b ⟨ha1, ha3⟩ ⟨hb1, hb3⟩
    constructor
    · show (a.toAdd + b.toAdd).1 = 0
      rw [Prod.fst_add, ha1, hb1, add_zero]
    · show ((a.toAdd + b.toAdd).2).2 = 0
      rw [Prod.snd_add, Prod.snd_add, ha3, hb3, add_zero]
  inv_mem' := by
    rintro a ⟨ha1, ha3⟩
    constructor
    · show (-a.toAdd).1 = 0
      rw [Prod.fst_neg, ha1, neg_zero]
    · show ((-a.toAdd).2).2 = 0
      rw [Prod.snd_neg, Prod.snd_neg, ha3, neg_zero]

private lemma bcoordMiddle_isClosed :
    IsClosed ((bcoordMiddle : Subgroup (Multiplicative (ZMod 2 × ℤ_[2] × ℤ_[2])))
      : Set (Multiplicative (ZMod 2 × ℤ_[2] × ℤ_[2]))) := by
  have hset : ((bcoordMiddle : Subgroup (Multiplicative (ZMod 2 × ℤ_[2] × ℤ_[2])))
        : Set (Multiplicative (ZMod 2 × ℤ_[2] × ℤ_[2])))
      = (fun z : Multiplicative (ZMod 2 × ℤ_[2] × ℤ_[2]) => z.toAdd.1) ⁻¹' {0}
        ∩ (fun z : Multiplicative (ZMod 2 × ℤ_[2] × ℤ_[2]) => z.toAdd.2.2) ⁻¹' {0} := rfl
  rw [hset]
  exact (isClosed_singleton.preimage (continuous_fst.comp continuous_toAdd)).inter
    (isClosed_singleton.preimage ((continuous_snd.comp continuous_snd).comp continuous_toAdd))

private lemma bCoordHom_Y : bCoordHom B d0Y = ofAdd ((0 : ZMod 2), (0 : ℤ_[2]), (1 : ℤ_[2])) := B.map_Y

/-- The conjugator words land in the `(0, ∗, 0)`-coordinate constraint: `λ`'s generators
`s³` and `s⁻³a⁻²` have trivial `ℤ/2`- and `Ȳ`-coordinates (`−2Ā` kills the torsion
coordinate). -/
lemma bCoord_lambda_mem (γ : Delta) : bCoordHom B (lambdaHom γ) ∈ bcoordMiddle := by
  have hcl : IsClosed ((bcoordMiddle.comap (bCoordHom B).toMonoidHom) : Set (D0 : Type)) :=
    bcoordMiddle_isClosed.preimage (bCoordHom B).continuous_toFun
  have hle := topClosure_closure_le_comap lambdaHom (S := {deltaP, deltaT})
    (M := bcoordMiddle.comap (bCoordHom B).toMonoidHom) hcl ?_
  · have hmem :
        γ ∈ (Subgroup.closure ({deltaP, deltaT} : Set (Delta : Type))).topologicalClosure := by
      rw [delta_pinned]
      exact Subgroup.mem_top γ
    have := hle hmem
    rw [Subgroup.mem_comap] at this
    exact Subgroup.mem_comap.mp this
  · rintro x (rfl | rfl)
    · rw [Subgroup.mem_comap]
      show bCoordHom B (lambdaHom deltaP) ∈ bcoordMiddle
      rw [lambdaHom_P, map_pow, bCoordHom_S]
      constructor
      · show ((3 : ℕ) • ((0 : ZMod 2), (1 : ℤ_[2]), (0 : ℤ_[2]))).1 = 0
        simp
      · show (((3 : ℕ) • ((0 : ZMod 2), (1 : ℤ_[2]), (0 : ℤ_[2]))).2).2 = 0
        simp
    · rw [Subgroup.mem_comap]
      show bCoordHom B (lambdaHom deltaT) ∈ bcoordMiddle
      rw [lambdaHom_T, map_mul, map_inv, map_inv, map_pow, map_pow, bCoordHom_S, bCoordHom_A]
      refine Subgroup.mul_mem _ (Subgroup.inv_mem _ ?_) (Subgroup.inv_mem _ ?_)
      · constructor
        · show ((3 : ℕ) • ((0 : ZMod 2), (1 : ℤ_[2]), (0 : ℤ_[2]))).1 = 0
          simp
        · show (((3 : ℕ) • ((0 : ZMod 2), (1 : ℤ_[2]), (0 : ℤ_[2]))).2).2 = 0
          simp
      · constructor
        · show ((2 : ℕ) • ((1 : ZMod 2), (-2 : ℤ_[2]), (0 : ℤ_[2]))).1 = 0
          decide
        · show (((2 : ℕ) • ((1 : ZMod 2), (-2 : ℤ_[2]), (0 : ℤ_[2]))).2).2 = 0
          simp

/-- Componentwise extensionality on the coordinate group. -/
lemma bcoord_ext {z w : Multiplicative (ZMod 2 × ℤ_[2] × ℤ_[2])}
    (h1 : z.toAdd.1 = w.toAdd.1) (h2 : z.toAdd.2.1 = w.toAdd.2.1)
    (h3 : z.toAdd.2.2 = w.toAdd.2.2) : z = w :=
  Multiplicative.toAdd.injective (Prod.ext h1 (Prod.ext h2 h3))

/-- **The `Ȳ`-row of `Ψ_u`** has the shape `(0, c, 1)`: the conjugators contribute only in
the `S̄`-coordinate. -/
lemma bCoord_psiHom_Y (R : PeripheralCyclotomicAction) (u : ℤ_[2]ˣ) :
    ∃ c : ℤ_[2],
      bCoordHom B (psiHom R u d0Y) = ofAdd ((0 : ZMod 2), c, (1 : ℤ_[2])) := by
  refine ⟨(bCoordHom B (psiHom R u d0Y)).toAdd.2.1, ?_⟩
  obtain ⟨hP1, hP3⟩ := bCoord_lambda_mem B (R.cP u)
  obtain ⟨hT1, hT3⟩ := bCoord_lambda_mem B (R.cT u)
  have hexpand : bCoordHom B (psiHom R u d0Y)
      = (bCoordHom B (lambdaHom (R.cP u)))⁻¹ * bCoordHom B d0Y
        * bCoordHom B (lambdaHom (R.cT u)) := by
    rw [psiHom_Y, map_mul, map_mul, map_inv]
  refine bcoord_ext ?_ rfl ?_
  · rw [hexpand, bCoordHom_Y]
    show ((-(bCoordHom B (lambdaHom (R.cP u))).toAdd
        + ((0 : ZMod 2), (0 : ℤ_[2]), (1 : ℤ_[2])))
        + (bCoordHom B (lambdaHom (R.cT u))).toAdd).1 = _
    rw [Prod.fst_add, Prod.fst_add, Prod.fst_neg, hP1, hT1]
    rfl
  · rw [hexpand, bCoordHom_Y]
    show (((-(bCoordHom B (lambdaHom (R.cP u))).toAdd
        + ((0 : ZMod 2), (0 : ℤ_[2]), (1 : ℤ_[2])))
        + (bCoordHom B (lambdaHom (R.cT u))).toAdd).2).2 = _
    rw [Prod.snd_add, Prod.snd_add, Prod.snd_add, Prod.snd_add, Prod.snd_neg, Prod.snd_neg,
      hP3, hT3]
    show -0 + 1 + 0 = ((0 : ZMod 2), (0 : ℤ_[2]), (1 : ℤ_[2])).2.2
    norm_num

include B in
/-- The coordinate group is pro-2 (continuous surjective image of `D₀^{ab}` under `B.e`). -/
lemma isProP_two_bcoord : IsProP 2 (Multiplicative (ZMod 2 × ℤ_[2] × ℤ_[2])) :=
  SectionThree.isProP_of_surjective B.e.toMulEquiv.toMonoidHom B.e.continuous_toFun
    (EquivLike.surjective B.e) SectionThree.isProP_two_topAb_D0

/-- Powering the `S̄`-line of the coordinate group multiplies the `S̄`-coordinate. -/
lemma zpowZtwo_bcoord_S (hBc : IsProP 2 (Multiplicative (ZMod 2 × ℤ_[2] × ℤ_[2])))
    (v w : ℤ_[2]) :
    zpowZtwo hBc (ofAdd ((0 : ZMod 2), v, (0 : ℤ_[2]))) w
      = ofAdd ((0 : ZMod 2), v * w, (0 : ℤ_[2])) := by
  set φ : Multiplicative ℤ_[2] →* Multiplicative (ZMod 2 × ℤ_[2] × ℤ_[2]) :=
    AddMonoidHom.toMultiplicative
      ((0 : ℤ_[2] →+ ZMod 2).prod ((AddMonoidHom.mulLeft v).prod (0 : ℤ_[2] →+ ℤ_[2]))) with hφ
  have hφcont : Continuous φ := by
    show Continuous fun w : Multiplicative ℤ_[2] =>
      ofAdd (((0 : ZMod 2), v * w.toAdd, (0 : ℤ_[2])))
    exact continuous_ofAdd.comp ((continuous_const.prodMk
      (((continuous_const_mul v).comp continuous_toAdd).prodMk continuous_const)))
  have h := zpowZtwoHom_unique hBc (φ := φ) hφcont w
  have h1 : φ (ofAdd (1 : ℤ_[2])) = ofAdd ((0 : ZMod 2), v, (0 : ℤ_[2])) := by
    show ofAdd (((0 : ZMod 2), v * (1 : ℤ_[2]), (0 : ℤ_[2]))) = _
    rw [mul_one]
  rw [h1] at h
  rw [← h]
  rfl

namespace SectionThree

/-- **Proposition 3.8, lifting half** (paper (18)/(19)): every `α_{u,b}` lifts to a continuous
automorphism of `D₀` — `Ψ_u` composed with the shear `Θ_{b'}`, `b' = (b − c(u))u⁻¹`.
Consumes axiom **B8**.  Declared here per the Prop. 3.2 precedent. -/
theorem prop_3_8_lift (u : ℤ_[2]ˣ) (b : ℤ_[2]) :
    ∃ Ψ : ContinuousMulEquiv (D0 : Type) (D0 : Type),
      B.e (abMk (Ψ d0A)) = Multiplicative.ofAdd (1, -2 * (u : ℤ_[2]), 0) ∧
      B.e (abMk (Ψ d0S)) = Multiplicative.ofAdd (0, (u : ℤ_[2]), 0) ∧
      B.e (abMk (Ψ d0Y)) = Multiplicative.ofAdd (0, b, 1) := by
  set R := peripheralCyclotomicAction with hR
  obtain ⟨c, hc⟩ := bCoord_psiHom_Y B R u
  set b' := (b - c) * ((u⁻¹ : ℤ_[2]ˣ) : ℤ_[2]) with hb'
  refine ⟨(thetaEquiv b').trans (psiEquiv R u), ?_, ?_, ?_⟩
  · show B.e (abMk (psiEquiv R u (thetaEquiv b' d0A))) = _
    rw [← bCoordHom_apply, psiEquiv_apply, thetaEquiv_apply, thetaHom_A]
    have hpush : psiHom R u (conjP d0A (sPow b'))
        = conjP (psiHom R u d0A) (psiHom R u (sPow b')) := by
      simp only [conjP, map_mul, map_inv]
    rw [hpush, bCoordHom_conjP, bCoord_psiHom_A]
  · show B.e (abMk (psiEquiv R u (thetaEquiv b' d0S))) = _
    rw [← bCoordHom_apply, psiEquiv_apply, thetaEquiv_apply, thetaHom_S, bCoord_psiHom_S]
  · show B.e (abMk (psiEquiv R u (thetaEquiv b' d0Y))) = _
    rw [← bCoordHom_apply, psiEquiv_apply, thetaEquiv_apply, thetaHom_Y, map_mul, map_mul, hc]
    have hsp : psiHom R u (sPow b') = zpowZtwo isProP_d0 (psiHom R u d0S) b' := by
      rw [sPow, map_zpowZtwo isProP_d0 isProP_d0 (psiHom R u) d0S b']
    have hbc : bCoordHom B (zpowZtwo isProP_d0 (psiHom R u d0S) b')
        = zpowZtwo (isProP_two_bcoord B) (bCoordHom B (psiHom R u d0S)) b' :=
      map_zpowZtwo isProP_d0 (isProP_two_bcoord B) (bCoordHom B) _ b'
    rw [hsp, hbc, bCoord_psiHom_S B R u, zpowZtwo_bcoord_S, ← ofAdd_add]
    congr 1
    have huu : (u : ℤ_[2]) * ((u⁻¹ : ℤ_[2]ˣ) : ℤ_[2]) = 1 := by
      rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
    refine Prod.ext (by simp) (Prod.ext ?_ (by simp))
    show c + (u : ℤ_[2]) * b' = b
    rw [hb']
    linear_combination (b - c) * huu

end SectionThree

end LiftHalf

end GQ2
