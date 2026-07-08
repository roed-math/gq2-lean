import GQ2.SectionThree
import GQ2.PeripheralAction
import GQ2.ZtwoPowering
import GQ2.FrattiniCriterion
import GQ2.FinitelyGenerated

/-!
# The anabelian bridge: B8 ⟹ Lemma 3.7  (P-08's escalated gap (a))

The paper's Lemma 3.7 constructs, for each `u ∈ ℤ₂ˣ`, an automorphism `Ψ_u` of `D₀` acting on
the abelianization by `Ā ↦ uĀ`, `S̄ ↦ uS̄`, out of B8's cyclotomic action `φ_u` on
`Δ = ⟨P,T⟩_pro-2`.  This file proves it (`GQ2.lemma_3_7`, statement **verbatim**
`SectionThree.lemma_3_7` — which should delegate here once its file's co-owned edits settle).

## The proof, reorganized (deviation note)

The paper (proof of Lemma 3.7) runs through the one-relator group `E□ = ⟨P,T,A | PTA²⟩_pro-2 ≅
⟨P,A⟩_pro-2`, a Tietze elimination, and a cube-root comparison.  We **inline** this scaffolding:

* B8's three conjugation identities combine (via `φ_u` being a homomorphism and `PTC = 1`) into
  the single `Δ`-identity `peripheral_identity` (*) below.
* The words `P ↦ s³`, `T ↦ s⁻³a⁻²` define a continuous hom `λ : Δ → D₀` (`lambdaHom`; freeness
  of `Δ` — no relator check).  Pushing (*) along `λ` gives exactly the conjugation identity that
  makes the marking `A ↦ (a^u)^{κ_C}`, `S ↦ (s^u)^{κ_P}`, `Y ↦ κ_P⁻¹ y κ_T` respect the
  Demushkin relator in its HNN form `y⁻¹sy = s⁻³a⁻²` (paper (16)) — so `Ψ_u` exists by the
  universal property of the presentation (`d0Lift`).
* Surjectivity is the pro-2 Frattini criterion (P-21 (iv)): in every index-2 quotient the
  `u`-powers act trivially (`u` is odd) and the conjugators die, so `Ψ_u`'s generator-images have
  the same images as the generators.  Hopficity (`profinite_hopfian`) upgrades to bijectivity.
* The cube-root comparison and the intermediate automorphism `θ_u` of the paper are not needed:
  their only role was to transit the identities from `Δ`-coordinates to `E`-coordinates, which
  the direct `λ`-push does.  (The `E□ ≅ ⟨P,A⟩` Tietze step is likewise absorbed.)

The `u`-th powers are B8's `x ^ᶻ ι u`; by the bundle's `hι_proj` pinning (the P-21 statement
amendment, `GQ2/PeripheralAction.lean` docstring) these are the 2-adic powers `zpowZtwo x u` on
every pro-2 group (`zpowHat_iota`).  The compatibility of that pinning with the original
`hι_one : ι 1 = ω₂` is **proved** here: `zhatProjTwo_omega2 : zhatProjTwo ω₂ = ofAdd 1`, via
`zpowHat_omega2_eq_self` (`x ^ᶻ ω₂ = x` on pro-2 groups — the T-06 idempotent acts as the
identity precisely on the pro-2 part).

Everything is at the standard three axioms plus (where marked) the B8 bundle argument.
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

/-- On a pro-2 group, the T-06 idempotent `ω₂ ∈ ℤ̂` powers every element to itself:
`x ^ᶻ ω₂ = x`.  (`ω₂ ≡ 1` on the pro-2 part; every finite quotient of a pro-2 group is a
2-group, where `powOmega2` is the identity.) -/
theorem zpowHat_omega2_eq_self (hP : IsProP 2 P) (x : P) : x ^ᶻ omega2 = x := by
  have hmem : ∀ U : OpenNormalSubgroup P, (x ^ᶻ omega2) * x⁻¹ ∈ U := by
    intro U
    haveI : DiscreteTopology (P ⧸ U.toSubgroup) := by
      refine discreteTopology_of_isOpen_singleton_one ?_
      have hpre : (QuotientGroup.mk : P → P ⧸ U.toSubgroup) ⁻¹' {1}
          = (U.toSubgroup : Set P) := by
        ext δ
        simp only [Set.mem_preimage, Set.mem_singleton_iff, SetLike.mem_coe,
          QuotientGroup.eq_one_iff]
      rw [← (QuotientGroup.isQuotientMap_mk U.toSubgroup).isOpen_preimage, hpre]
      exact U.isOpen'
    haveI : Finite (P ⧸ U.toSubgroup) := Subgroup.quotient_finite_of_isOpen _ U.isOpen'
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
(via the `hι_proj` pinning and P-21's `zpowHat_eq_zpowZtwo`). -/
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

@[simp] lemma conjP_mul (x y c : G) : conjP x c * conjP y c = conjP (x * y) c := by
  simp [conjP, mul_assoc]

@[simp] lemma conjP_inv (x c : G) : (conjP x c)⁻¹ = conjP x⁻¹ c := by
  simp [conjP, mul_assoc]

@[simp] lemma conjP_pow (x c : G) (n : ℕ) : conjP x c ^ n = conjP (x ^ n) c := by
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

@[simp] lemma deltaLift_P (hH : IsProP 2 H) (m : Fin 2 → H) :
    deltaLift hH m deltaP = m 0 := by
  show ((maxProPHomEquiv hH).symm _)
    (maxProPMk 2 (FreeProfiniteGroup (Fin 2)) (FreeProfiniteGroup.of 0)) = m 0
  rw [maxProPHomEquiv_symm_apply_maxProPMk]
  exact FreeProfiniteGroup.homEquiv_symm_of _ _ _

@[simp] lemma deltaLift_T (hH : IsProP 2 H) (m : Fin 2 → H) :
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
          rw [Set.mem_singleton_iff.mp hr, SetLike.mem_coe, MonoidHom.mem_ker]
          exact hone
        · have hker : (f.toMonoidHom.ker : Set (FreeProfiniteGroup (Fin 3)))
              = ⇑f ⁻¹' {1} := by
            ext x
            simp only [SetLike.mem_coe, MonoidHom.mem_ker, Set.mem_preimage,
              Set.mem_singleton_iff]
            rfl
          rw [hker]
          exact isClosed_singleton.preimage f.continuous_toFun))

@[simp] lemma d0Lift_A (hH : IsProP 2 H) (m : Fin 3 → H)
    (hrel : m 0 ^ 2 * m 1 ^ 4 * commP (m 1) (m 2) = 1) :
    d0Lift hH m hrel d0A = m 0 := by
  show ((maxProPHomEquiv hH).symm _) (maxProPMk 2 D0Full
    (quotientMk (relatorSubgroup {d0Relator}) (FreeProfiniteGroup.of 0))) = m 0
  rw [maxProPHomEquiv_symm_apply_maxProPMk]
  exact (quotientLift_quotientMk _ _ _ _).trans (FreeProfiniteGroup.homEquiv_symm_of _ _ _)

@[simp] lemma d0Lift_S (hH : IsProP 2 H) (m : Fin 3 → H)
    (hrel : m 0 ^ 2 * m 1 ^ 4 * commP (m 1) (m 2) = 1) :
    d0Lift hH m hrel d0S = m 1 := by
  show ((maxProPHomEquiv hH).symm _) (maxProPMk 2 D0Full
    (quotientMk (relatorSubgroup {d0Relator}) (FreeProfiniteGroup.of 1))) = m 1
  rw [maxProPHomEquiv_symm_apply_maxProPMk]
  exact (quotientLift_quotientMk _ _ _ _).trans (FreeProfiniteGroup.homEquiv_symm_of _ _ _)

@[simp] lemma d0Lift_Y (hH : IsProP 2 H) (m : Fin 3 → H)
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
/-- The index-2 quotient is commutative. -/
lemma quotient_mul_comm (z w : K ⧸ M.toSubgroup) : z * w = w * z := by
  haveI : Finite (K ⧸ M.toSubgroup) := Subgroup.quotient_finite_of_isOpen _ M.isOpen'
  have hcard : Nat.card (K ⧸ M.toSubgroup) = 2 := by
    rw [← Subgroup.index_eq_card]; exact hM
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI := isCyclic_of_prime_card (p := 2) hcard
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := K ⧸ M.toSubgroup)
  obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp (hg z)
  obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp (hg w)
  rw [← hi, ← hj, ← zpow_add, ← zpow_add, add_comm]

include hM in
/-- Squares die in the index-2 quotient. -/
lemma quotient_sq_eq_one (z : K ⧸ M.toSubgroup) : z ^ 2 = 1 := by
  haveI : Finite (K ⧸ M.toSubgroup) := Subgroup.quotient_finite_of_isOpen _ M.isOpen'
  have hcard : Nat.card (K ⧸ M.toSubgroup) = 2 := by
    rw [← Subgroup.index_eq_card]; exact hM
  have hdvd : orderOf z ∣ 2 := hcard ▸ orderOf_dvd_natCard z
  exact orderOf_dvd_iff_pow_eq_one.mp hdvd

include hM in
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
/-- **B8's `ι`-powers die in index-2 quotients**: `q(x ^ᶻ ι u) = q(x)` (`u` is odd). -/
lemma quotient_map_zpowHat_iota (R : PeripheralCyclotomicAction) (x : K) (u : ℤ_[2]ˣ) :
    QuotientGroup.mk' M.toSubgroup (x ^ᶻ R.ι u) = QuotientGroup.mk' M.toSubgroup x := by
  haveI := discreteTopology_quotient_openNormal M
  haveI : Finite (K ⧸ M.toSubgroup) := Subgroup.quotient_finite_of_isOpen _ M.isOpen'
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

@[simp] lemma lambdaHom_P : lambdaHom deltaP = d0S ^ 3 :=
  deltaLift_P _ _

@[simp] lemma lambdaHom_T : lambdaHom deltaT = (d0S ^ 3)⁻¹ * (d0A ^ 2)⁻¹ :=
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

@[simp] lemma psiHom_A : psiHom R u d0A = conjP (d0A ^ᶻ R.ι u) (lambdaHom (R.cC u)) :=
  d0Lift_A _ _ _

@[simp] lemma psiHom_S : psiHom R u d0S = conjP (d0S ^ᶻ R.ι u) (lambdaHom (R.cP u)) :=
  d0Lift_S _ _ _

@[simp] lemma psiHom_Y :
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
  · have hmem : γ ∈ (Subgroup.closure ({deltaP, deltaT} : Set (Delta : Type))).topologicalClosure := by
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
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine surjective_of_forall_index_p_quotient_surjective isProP_d0 (psiHom R u) ?_
  intro M hM
  haveI := discreteTopology_quotient_openNormal M
  haveI : Finite ((D0 : Type) ⧸ M.toSubgroup) := Subgroup.quotient_finite_of_isOpen _ M.isOpen'
  have hcard : Nat.card ((D0 : Type) ⧸ M.toSubgroup) = 2 := by
    rw [← Subgroup.index_eq_card]; exact hM
  haveI : Fact (Nat.Prime (Nat.card ((D0 : Type) ⧸ M.toSubgroup))) := ⟨hcard ▸ Nat.prime_two⟩
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
      rw [psiHom_Y, map_mul, map_mul, map_inv, hκ (R.cP u), hκ (R.cT u), inv_one, one_mul,
        mul_one] at h
      exact h
    -- … hence everything: the quotient is trivial, contradicting index 2.
    have hkerAll := topClosure_closure_le_ker
      (⟨QuotientGroup.mk' M.toSubgroup, continuous_quot_mk⟩ :
        ContinuousMonoidHom (D0 : Type) ((D0 : Type) ⧸ M.toSubgroup))
      (S := {d0A, d0S, d0Y}) (by rintro x (rfl | rfl | rfl) <;> assumption)
    haveI : Nontrivial ((D0 : Type) ⧸ M.toSubgroup) := by
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

@[simp] lemma psiEquiv_apply (x : (D0 : Type)) : psiEquiv R u x = psiHom R u x := rfl

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

lemma bCoordHom_apply (x : (D0 : Type)) : bCoordHom B x = B.e (abMk x) := rfl

lemma bCoordHom_conjP (x c : (D0 : Type)) : bCoordHom B (conjP x c) = bCoordHom B x := by
  rw [conjP, map_mul, map_mul, map_inv, mul_comm ((bCoordHom B c)⁻¹) (bCoordHom B x),
    mul_assoc, inv_mul_cancel, mul_one]

lemma bCoordHom_S : bCoordHom B d0S = ofAdd ((0 : ZMod 2), (1 : ℤ_[2]), (0 : ℤ_[2])) :=
  B.map_S

lemma bCoordHom_A : bCoordHom B d0A = ofAdd ((1 : ZMod 2), (-2 : ℤ_[2]), (0 : ℤ_[2])) := by
  have hsplit : d0A = (d0A * d0S ^ 2) * (d0S ^ 2)⁻¹ := by group
  have hφt : bCoordHom B (d0A * d0S ^ 2)
      = ofAdd ((1 : ZMod 2), (0 : ℤ_[2]), (0 : ℤ_[2])) := B.map_t
  rw [hsplit, map_mul, map_inv, map_pow, hφt, bCoordHom_S]
  rw [← ofAdd_nsmul, ← ofAdd_neg, ← ofAdd_add]
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
P-09 precedent (`GQ2/Prop32.lean`). -/
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

lemma sPow_mul_neg (b : ℤ_[2]) : sPow b * sPow (-b) = 1 := by
  rw [sPow, sPow, ← zpowZtwo_add, add_neg_cancel, SectionThree.zpowZtwo_zero]

/-- Ordinary `S`-powers commute with `S^b`. -/
lemma commute_pow_sPow (n : ℕ) (b : ℤ_[2]) : Commute (d0S ^ n) (sPow b) := by
  have h1 : d0S ^ n = zpowZtwo isProP_d0 d0S ((n : ℕ) : ℤ_[2]) := (zpowZtwo_natCast _ _ _).symm
  show d0S ^ n * sPow b = sPow b * d0S ^ n
  rw [h1, sPow, ← zpowZtwo_add, ← zpowZtwo_add, add_comm]

lemma conjP_pow_sPow (n : ℕ) (b : ℤ_[2]) : conjP (d0S ^ n) (sPow b) = d0S ^ n := by
  rw [conjP, mul_assoc, (commute_pow_sPow n b).eq, ← mul_assoc, inv_mul_cancel, one_mul]

/-- Composing conjugations multiplies the conjugators. -/
lemma conjP_conjP {G : Type*} [Group G] (x c d : G) :
    conjP (conjP x c) d = conjP x (c * d) := by
  simp only [conjP]
  group

@[simp] lemma conjP_one {G : Type*} [Group G] (x : G) : conjP x 1 = x := by
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

@[simp] lemma thetaHom_A (b : ℤ_[2]) : thetaHom b d0A = conjP d0A (sPow b) := d0Lift_A _ _ _
@[simp] lemma thetaHom_S (b : ℤ_[2]) : thetaHom b d0S = d0S := d0Lift_S _ _ _
@[simp] lemma thetaHom_Y (b : ℤ_[2]) : thetaHom b d0Y = d0Y * sPow b := d0Lift_Y _ _ _

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

@[simp] lemma thetaEquiv_apply (b : ℤ_[2]) (x : (D0 : Type)) :
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

lemma bcoordMiddle_isClosed :
    IsClosed ((bcoordMiddle : Subgroup (Multiplicative (ZMod 2 × ℤ_[2] × ℤ_[2])))
      : Set (Multiplicative (ZMod 2 × ℤ_[2] × ℤ_[2]))) := by
  have hset : ((bcoordMiddle : Subgroup (Multiplicative (ZMod 2 × ℤ_[2] × ℤ_[2])))
        : Set (Multiplicative (ZMod 2 × ℤ_[2] × ℤ_[2])))
      = (fun z : Multiplicative (ZMod 2 × ℤ_[2] × ℤ_[2]) => z.toAdd.1) ⁻¹' {0}
        ∩ (fun z : Multiplicative (ZMod 2 × ℤ_[2] × ℤ_[2]) => z.toAdd.2.2) ⁻¹' {0} := rfl
  rw [hset]
  exact (isClosed_singleton.preimage (continuous_fst.comp continuous_toAdd)).inter
    (isClosed_singleton.preimage ((continuous_snd.comp continuous_snd).comp continuous_toAdd))

lemma bCoordHom_Y : bCoordHom B d0Y = ofAdd ((0 : ZMod 2), (0 : ℤ_[2]), (1 : ℤ_[2])) := B.map_Y

/-- The conjugator words land in the `(0, ∗, 0)`-coordinate constraint: `λ`'s generators
`s³` and `s⁻³a⁻²` have trivial `ℤ/2`- and `Ȳ`-coordinates (`−2Ā` kills the torsion
coordinate). -/
lemma bCoord_lambda_mem (γ : Delta) : bCoordHom B (lambdaHom γ) ∈ bcoordMiddle := by
  have hcl : IsClosed ((bcoordMiddle.comap (bCoordHom B).toMonoidHom) : Set (D0 : Type)) :=
    bcoordMiddle_isClosed.preimage (bCoordHom B).continuous_toFun
  have hle := topClosure_closure_le_comap lambdaHom (S := {deltaP, deltaT})
    (M := bcoordMiddle.comap (bCoordHom B).toMonoidHom) hcl ?_
  · have hmem : γ ∈ (Subgroup.closure ({deltaP, deltaT} : Set (Delta : Type))).topologicalClosure := by
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
Consumes axiom **B8**.  Declared here per the P-09 precedent. -/
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

/-! ## Proposition 3.8, classification half

Every χ₀-preserving continuous automorphism of `B = D₀^{ab}` is `α_{u,b}` for a unique
`(u, b) ∈ ℤ₂ˣ × ℤ₂` (paper (18)).  Engine: P-07's coordinate surjectivity `D0ab_coord`,
the torsion analysis of `t`, and P-21's `η`-injectivity; the `(−1)^ε`-component is killed by
the mod-4 argument (`η`-powers are `≡ 1 (mod 4)`, `−1` is not). -/

section ClassificationHalf

open SectionThree

-- The `topAbelianization` instances beyond the P-06 globals are file-local (as in
-- `GQ2/SectionThree.lean`, and for the same reason: a generic global instance perturbs
-- unrelated quotient instance resolution).
noncomputable local instance instCommGroupTopAbBridge {G : Type*} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] : CommGroup (topAbelianization G) where
  __ := (inferInstance : Group (topAbelianization G))
  mul_comm := by
    intro x y
    obtain ⟨a, rfl⟩ := abMk_surjective (G := G) x
    obtain ⟨b, rfl⟩ := abMk_surjective (G := G) y
    rw [← map_mul, ← map_mul]
    show QuotientGroup.mk (a * b) = QuotientGroup.mk (b * a)
    refine (QuotientGroup.eq).mpr ?_
    have hcomm : (a * b)⁻¹ * (b * a) = b⁻¹ * a⁻¹ * b * a := by group
    rw [hcomm]
    apply Subgroup.le_topologicalClosure
    have hmem := Subgroup.commutator_mem_commutator (G := G)
      (Subgroup.mem_top b⁻¹) (Subgroup.mem_top a⁻¹)
    rw [commutator_def]
    simpa [commutatorElement_def] using hmem

local instance instCompactSpaceTopAbBridge {G : Type*} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G] :
    CompactSpace (topAbelianization G) :=
  inferInstanceAs (CompactSpace (G ⧸ (commutator G).topologicalClosure))

local instance instT2SpaceTopAbBridge {G : Type*} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G] :
    T2Space (topAbelianization G) :=
  haveI : IsClosed ((commutator G).topologicalClosure : Set G) :=
    (commutator G).isClosed_topologicalClosure
  inferInstanceAs (T2Space (G ⧸ (commutator G).topologicalClosure))

local instance instTotallyDisconnectedSpaceTopAbBridge {G : Type*} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G] :
    TotallyDisconnectedSpace (topAbelianization G) :=
  haveI : IsClosed ((commutator G).topologicalClosure : Set G) :=
    (commutator G).isClosed_topologicalClosure
  inferInstanceAs (TotallyDisconnectedSpace (G ⧸ (commutator G).topologicalClosure))

variable (B : SectionThree.BDecomposition)

/-- Shorthand: `S̄`-powers in `D₀^{ab}`. -/
noncomputable def sBar (c : ℤ_[2]) : topAbelianization (D0 : Type) :=
  zpowZtwo isProP_two_topAb_D0 (abMk d0S) c

/-- `B.e` reads `S̄`-powers in the second coordinate. -/
lemma bE_sBar (c : ℤ_[2]) :
    B.e (sBar c) = ofAdd ((0 : ZMod 2), c, (0 : ℤ_[2])) := by
  have hnat : B.e (sBar c)
      = zpowZtwo (isProP_two_bcoord B) (B.e (abMk d0S)) c := by
    rw [sBar]
    exact map_zpowZtwo isProP_two_topAb_D0 (isProP_two_bcoord B)
      ⟨B.e.toMulEquiv.toMonoidHom, B.e.continuous_toFun⟩ _ c
  rw [hnat, B.map_S, zpowZtwo_bcoord_S, one_mul]

include B in
/-- `S̄`-powers are injective in the exponent. -/
lemma sBar_injective : Function.Injective sBar := by
  intro c₁ c₂ h
  have hBe : B.e (sBar c₁) = B.e (sBar c₂) := congrArg (⇑B.e) h
  rw [bE_sBar B, bE_sBar B] at hBe
  exact congrArg (fun z => (Multiplicative.toAdd z).2.1) hBe

include B in
/-- The 2-torsion of `D₀^{ab}` is `{1, t}`, `t = abMk (A·S²)` (read off the coordinates:
the `ℤ₂`-components of a square-trivial element vanish). -/
lemma sq_eq_one_iff (z : topAbelianization (D0 : Type)) :
    z ^ 2 = 1 ↔ z = 1 ∨ z = abMk (d0A * d0S ^ 2) := by
  constructor
  · intro h
    have hBe : (B.e z) ^ 2 = 1 := by rw [← map_pow, h, map_one]
    have hcomp : (2 : ℕ) • (Multiplicative.toAdd (B.e z)) = 0 := by
      have h' := congrArg Multiplicative.toAdd hBe
      rwa [show Multiplicative.toAdd ((B.e z) ^ 2)
        = (2 : ℕ) • (Multiplicative.toAdd (B.e z)) from rfl] at h'
    have hx : (Multiplicative.toAdd (B.e z)).2.1 = 0 := by
      have h21 := congrArg (fun p : ZMod 2 × ℤ_[2] × ℤ_[2] => p.2.1) hcomp
      simp only [Prod.smul_snd, Prod.smul_fst, Prod.snd_zero, Prod.fst_zero] at h21
      have h21' : (2 : ℤ_[2]) * (Multiplicative.toAdd (B.e z)).2.1 = 0 := by
        rw [← h21, nsmul_eq_mul]
        norm_num
      exact (mul_eq_zero.mp h21').resolve_left (by norm_num)
    have hy : (Multiplicative.toAdd (B.e z)).2.2 = 0 := by
      have h22 := congrArg (fun p : ZMod 2 × ℤ_[2] × ℤ_[2] => p.2.2) hcomp
      simp only [Prod.smul_snd, Prod.snd_zero] at h22
      have h22' : (2 : ℤ_[2]) * (Multiplicative.toAdd (B.e z)).2.2 = 0 := by
        rw [← h22, nsmul_eq_mul]
        norm_num
      exact (mul_eq_zero.mp h22').resolve_left (by norm_num)
    rcases (by decide : ∀ c : ZMod 2, c = 0 ∨ c = 1) (Multiplicative.toAdd (B.e z)).1
      with hε | hε
    · left
      have hz1 : B.e z = B.e 1 := by
        rw [map_one]
        exact bcoord_ext hε hx hy
      exact EquivLike.injective B.e hz1
    · right
      have hzt : B.e z = B.e (abMk (d0A * d0S ^ 2)) := by
        rw [B.map_t]
        exact bcoord_ext hε hx hy
      exact EquivLike.injective B.e hzt
  · rintro (rfl | rfl)
    · exact one_pow 2
    · have hsq : (B.e (abMk (d0A * d0S ^ 2))) ^ 2 = B.e 1 := by
        rw [B.map_t, map_one, pow_two, ← ofAdd_add]
        refine congrArg ofAdd (Prod.ext ?_ (Prod.ext ?_ ?_))
        · show (1 : ZMod 2) + 1 = 0
          decide
        · show (0 : ℤ_[2]) + 0 = 0
          norm_num
        · show (0 : ℤ_[2]) + 0 = 0
          norm_num
      have hpow : B.e ((abMk (d0A * d0S ^ 2) : topAbelianization (D0 : Type)) ^ 2) = B.e 1 := by
        rw [map_pow]
        exact hsq
      exact EquivLike.injective B.e hpow

variable (ξ : ContinuousMulEquiv (topAbelianization (D0 : Type)) (topAbelianization (D0 : Type)))

/-- `ξ`-naturality of 2-adic powers. -/
lemma xi_zpow (x : topAbelianization (D0 : Type)) (c : ℤ_[2]) :
    ξ (zpowZtwo isProP_two_topAb_D0 x c) = zpowZtwo isProP_two_topAb_D0 (ξ x) c :=
  map_zpowZtwo isProP_two_topAb_D0 isProP_two_topAb_D0
    ⟨ξ.toMulEquiv.toMonoidHom, ξ.continuous_toFun⟩ x c

include B in
/-- Any continuous automorphism fixes `t` (the unique nontrivial 2-torsion element). -/
lemma xi_fixes_t : ξ (abMk (d0A * d0S ^ 2)) = abMk (d0A * d0S ^ 2) := by
  have ht2 : (abMk (d0A * d0S ^ 2) : topAbelianization (D0 : Type)) ^ 2 = 1 :=
    (sq_eq_one_iff B _).mpr (Or.inr rfl)
  have hξ2 : (ξ (abMk (d0A * d0S ^ 2))) ^ 2 = 1 := by
    rw [← map_pow, ht2, map_one]
  rcases (sq_eq_one_iff B _).mp hξ2 with h1 | ht
  · exfalso
    have hteq : (abMk (d0A * d0S ^ 2) : topAbelianization (D0 : Type)) = 1 := by
      have := congrArg ξ.symm h1
      rwa [ContinuousMulEquiv.symm_apply_apply, map_one] at this
    have hBet := congrArg B.e hteq
    rw [B.map_t, map_one] at hBet
    have hcomp := congrArg (fun z => (Multiplicative.toAdd z).1) hBet
    exact absurd hcomp (by decide)
  · exact ht

/-- The paper's `η ^ w ≡ 1 (mod 4)` (the image of `zpowZtwo η` lies in `1 + 4ℤ₂`). -/
lemma eta_pow_mod4 (y₀ : ℤ_[2]ˣ) (hy₀ : (y₀ : ℤ_[2]) = -3) (w : ℤ_[2]) :
    (PadicInt.toZModPow (p := 2) 2
      ((zpowZtwo isProP_two_unitsPadicInt y₀⁻¹ w : ℤ_[2]ˣ) : ℤ_[2]) : ZMod 4) = 1 := by
  letI : TopologicalSpace (ZMod 4) := ⊥
  letI : DiscreteTopology (ZMod 4) := ⟨rfl⟩
  have hcont_toZMod : Continuous (PadicInt.toZModPow (p := 2) 2 : ℤ_[2] → ZMod 4) := by
    rw [continuous_def]
    intro T _
    exact isOpen_preimage_toZModPow 2 T
  have hy0mod : (PadicInt.toZModPow (p := 2) 2 ((y₀ : ℤ_[2])) : ZMod 4) = 1 := by
    rw [hy₀, show (-3 : ℤ_[2]) = ((-3 : ℤ) : ℤ_[2]) by push_cast; ring, map_intCast]
    decide
  have hinv_mod : (PadicInt.toZModPow (p := 2) 2 ((y₀⁻¹ : ℤ_[2]ˣ) : ℤ_[2]) : ZMod 4) = 1 := by
    have hmul : ((y₀⁻¹ : ℤ_[2]ˣ) : ℤ_[2]) * ((y₀ : ℤ_[2]ˣ) : ℤ_[2]) = 1 := by
      rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
    have h := congrArg (PadicInt.toZModPow (p := 2) 2) hmul
    rw [map_mul, map_one, hy0mod, mul_one] at h
    exact h
  set f : Multiplicative ℤ_[2] →* ZMod 4 :=
    (PadicInt.toZModPow (p := 2) 2 : ℤ_[2] →+* ZMod 4).toMonoidHom.comp
      ((Units.coeHom ℤ_[2]).comp
        (zpowZtwoHom isProP_two_unitsPadicInt y₀⁻¹).toMonoidHom) with hfdef
  have hfcont : Continuous f :=
    hcont_toZMod.comp (Units.continuous_val.comp
      (zpowZtwoHom isProP_two_unitsPadicInt y₀⁻¹).continuous_toFun)
  have hf1 : f = (1 : Multiplicative ℤ_[2] →* ZMod 4) := by
    refine multPadicIntHom_ext hfcont continuous_const ?_
    show (PadicInt.toZModPow (p := 2) 2)
      ((zpowZtwoHom isProP_two_unitsPadicInt y₀⁻¹ (ofAdd (1 : ℤ_[2])) : ℤ_[2]ˣ) : ℤ_[2]) = 1
    rw [zpowZtwoHom_ofAdd_one]
    exact hinv_mod
  have hw := DFunLike.congr_fun hf1 (ofAdd w)
  rw [MonoidHom.one_apply] at hw
  exact hw

/-- **The χ-row extraction**: from `(−1)^r · η^y = η^w` conclude `2 ∣ a` (`r = a mod 2 = 0`,
by the mod-4 elimination) and `y = w` (`η`-injectivity, P-21 (iii)). -/
lemma chi_row_extract (y₀ : ℤ_[2]ˣ) (hy₀ : (y₀ : ℤ_[2]) = -3) (a y w : ℤ_[2])
    (h : (-1 : ℤ_[2]ˣ) ^ (PadicInt.toZModPow (p := 2) 1 a).val
        * zpowZtwo isProP_two_unitsPadicInt y₀⁻¹ y
      = zpowZtwo isProP_two_unitsPadicInt y₀⁻¹ w) :
    (2 : ℤ_[2]) ∣ a ∧ y = w := by
  have hrlt : (PadicInt.toZModPow (p := 2) 1 a).val < 2 := by
    have hlt := ZMod.val_lt (PadicInt.toZModPow (p := 2) 1 a)
    simpa using hlt
  rcases (by omega : (PadicInt.toZModPow (p := 2) 1 a).val = 0
      ∨ (PadicInt.toZModPow (p := 2) 1 a).val = 1) with hr0 | hr1
  · rw [hr0, pow_zero, one_mul] at h
    constructor
    · have hval0 : (PadicInt.toZModPow (p := 2) 1 a) = 0 := by
        haveI : NeZero (2 ^ 1) := ⟨by norm_num⟩
        exact (ZMod.val_eq_zero _).mp hr0
      have hker : a ∈ RingHom.ker (PadicInt.toZModPow (p := 2) 1) := hval0
      rw [PadicInt.ker_toZModPow, pow_one, Ideal.mem_span_singleton] at hker
      exact hker
    · exact zpowZtwo_injective_neg_three_inv y₀ hy₀ h
  · exfalso
    rw [hr1, pow_one] at h
    have hL := congrArg (fun v : ℤ_[2]ˣ => (PadicInt.toZModPow (p := 2) 2 ((v : ℤ_[2])) : ZMod 4)) h
    rw [show (((-1 : ℤ_[2]ˣ) * zpowZtwo isProP_two_unitsPadicInt y₀⁻¹ y : ℤ_[2]ˣ) : ℤ_[2])
        = -(((zpowZtwo isProP_two_unitsPadicInt y₀⁻¹ y : ℤ_[2]ˣ)) : ℤ_[2]) by push_cast; ring,
      map_neg, eta_pow_mod4 y₀ hy₀, eta_pow_mod4 y₀ hy₀] at hL
    exact absurd hL (by decide)

/-- Abelianized relation: `Ā² S̄⁴ = 1` in `D₀^{ab}`. -/
lemma abMk_relation :
    ((abMk d0A : topAbelianization (D0 : Type))) ^ 2 * (abMk d0S) ^ 4 = 1 := by
  have hcommP : abMk (commP d0S d0Y) = (1 : topAbelianization (D0 : Type)) := by
    rw [commP, map_mul, map_mul, map_mul, map_inv, map_inv,
      mul_comm ((abMk d0S)⁻¹ : topAbelianization (D0 : Type)) ((abMk d0Y)⁻¹)]
    group
  have h2 : abMk (d0A ^ 2 * d0S ^ 4 * commP d0S d0Y) = (1 : topAbelianization (D0 : Type)) := by
    rw [d0_relation]
    exact map_one abMk
  rw [map_mul, map_mul, map_pow, map_pow, hcommP, mul_one] at h2
  exact h2

/-- Even `Ā`-powers are `S̄`-powers: `Ā^{2a₁} = S̄^{−4a₁}`. -/
lemma aPow_even (a : ℤ_[2]) (h2 : (2 : ℤ_[2]) ∣ a) :
    zpowZtwo isProP_two_topAb_D0 (abMk d0A) a = sBar (-2 * a) := by
  obtain ⟨a₁, rfl⟩ := h2
  have hstep1 : zpowZtwo isProP_two_topAb_D0 (abMk d0A) (2 * a₁)
      = zpowZtwo isProP_two_topAb_D0 (zpowZtwo isProP_two_topAb_D0 (abMk d0A) 2) a₁ :=
    (zpowZtwo_zpowZtwo _ _ _ _).symm
  have hstep2 : zpowZtwo isProP_two_topAb_D0 (abMk d0A) (2 : ℤ_[2]) = (abMk d0A) ^ (2 : ℕ) := by
    have hcast : ((2 : ℤ_[2])) = (((2 : ℕ)) : ℤ_[2]) := by norm_num
    rw [hcast, zpowZtwo_natCast]
  have hstep3 : ((abMk d0A : topAbelianization (D0 : Type))) ^ (2 : ℕ)
      = zpowZtwo isProP_two_topAb_D0 (abMk d0S) (-4 : ℤ_[2]) := by
    have hrel := abMk_relation
    have hA2 : ((abMk d0A : topAbelianization (D0 : Type))) ^ (2 : ℕ)
        = (((abMk d0S : topAbelianization (D0 : Type))) ^ (4 : ℕ))⁻¹ := by
      rw [eq_inv_iff_mul_eq_one]
      exact hrel
    have hS4 : (((abMk d0S : topAbelianization (D0 : Type))) ^ (4 : ℕ))⁻¹
        = zpowZtwo isProP_two_topAb_D0 (abMk d0S) (-4 : ℤ_[2]) := by
      have hcast : ((-4 : ℤ_[2])) = (((-4 : ℤ)) : ℤ_[2]) := by push_cast; ring
      rw [hcast, zpowZtwo_intCast]
      rw [show ((-4 : ℤ)) = -((4 : ℕ) : ℤ) by norm_num, zpow_neg, zpow_natCast]
    rw [hA2, hS4]
  rw [hstep1, hstep2, hstep3, sBar, zpowZtwo_zpowZtwo]
  congr 1
  ring

/-- The `χ`-value on coordinates: `χ(Ā^a S̄^s Ȳ^y) = (−1)^{a mod 2} η^y`. -/
lemma chi_coord (χ : topAbelianization (D0 : Type) →* ℤ_[2]ˣ) (hχ : Continuous χ)
    (y₀ : ℤ_[2]ˣ)
    (hχA : χ (abMk d0A) = -1) (hχS : χ (abMk d0S) = 1) (hχY' : χ (abMk d0Y) = y₀⁻¹)
    (a s y : ℤ_[2]) :
    χ (zpowZtwo isProP_two_topAb_D0 (abMk d0A) a
        * zpowZtwo isProP_two_topAb_D0 (abMk d0S) s
        * zpowZtwo isProP_two_topAb_D0 (abMk d0Y) y)
      = (-1 : ℤ_[2]ˣ) ^ (PadicInt.toZModPow (p := 2) 1 a).val
        * zpowZtwo isProP_two_unitsPadicInt y₀⁻¹ y := by
  have hχnat : ∀ (x : topAbelianization (D0 : Type)) (u : ℤ_[2]),
      χ (zpowZtwo isProP_two_topAb_D0 x u)
        = zpowZtwo isProP_two_unitsPadicInt (χ x) u := fun x u =>
    map_zpowZtwo isProP_two_topAb_D0 isProP_two_unitsPadicInt
      (⟨χ, hχ⟩ : ContinuousMonoidHom (topAbelianization (D0 : Type)) ℤ_[2]ˣ) x u
  have hsq : (-1 : ℤ_[2]ˣ) ^ 2 = 1 := by
    rw [pow_two, ← Units.val_eq_one]
    push_cast
    ring
  rw [map_mul, map_mul, hχnat, hχnat, hχnat, hχA, hχS, hχY',
    zpowZtwo_one_base, mul_one,
    zpowZtwo_of_sq_eq_one isProP_two_unitsPadicInt (-1) hsq a]

/-- The `S̄`-row of a χ-preserving automorphism is a pure `S̄`-power. -/
lemma xi_S_row (χ : topAbelianization (D0 : Type) →* ℤ_[2]ˣ) (hχ : Continuous χ)
    (y₀ : ℤ_[2]ˣ) (hy₀ : (y₀ : ℤ_[2]) = -3)
    (hχA : χ (abMk d0A) = -1) (hχS : χ (abMk d0S) = 1) (hχY' : χ (abMk d0Y) = y₀⁻¹)
    (hpres : ∀ x, χ (ξ x) = χ x) :
    ∃ u : ℤ_[2], ξ (abMk d0S) = sBar u := by
  obtain ⟨a, s, y, hzeq⟩ := D0ab_coord (ξ (abMk d0S))
  have hχval : χ (ξ (abMk d0S)) = 1 := by rw [hpres, hχS]
  rw [hzeq, chi_coord χ hχ y₀ hχA hχS hχY'] at hχval
  obtain ⟨h2a, hy0⟩ := chi_row_extract y₀ hy₀ a y 0
    (by rw [hχval, SectionThree.zpowZtwo_zero])
  refine ⟨-2 * a + s, ?_⟩
  rw [hzeq, hy0, SectionThree.zpowZtwo_zero, mul_one, aPow_even a h2a, sBar, sBar,
    ← zpowZtwo_add]

/-- The `Ȳ`-row of a χ-preserving automorphism is `S̄`-power times `Ȳ`. -/
lemma xi_Y_row (χ : topAbelianization (D0 : Type) →* ℤ_[2]ˣ) (hχ : Continuous χ)
    (y₀ : ℤ_[2]ˣ) (hy₀ : (y₀ : ℤ_[2]) = -3)
    (hχA : χ (abMk d0A) = -1) (hχS : χ (abMk d0S) = 1) (hχY' : χ (abMk d0Y) = y₀⁻¹)
    (hpres : ∀ x, χ (ξ x) = χ x) :
    ∃ b : ℤ_[2], ξ (abMk d0Y) = sBar b * abMk d0Y := by
  obtain ⟨a, s, y, hzeq⟩ := D0ab_coord (ξ (abMk d0Y))
  have hχval : χ (ξ (abMk d0Y)) = y₀⁻¹ := by rw [hpres, hχY']
  rw [hzeq, chi_coord χ hχ y₀ hχA hχS hχY'] at hχval
  obtain ⟨h2a, hy1⟩ := chi_row_extract y₀ hy₀ a y 1
    (by rw [hχval, zpowZtwo_one_exp])
  refine ⟨-2 * a + s, ?_⟩
  rw [hzeq, hy1, zpowZtwo_one_exp, aPow_even a h2a, sBar, sBar, ← zpowZtwo_add]

namespace SectionThree

/-- **Proposition 3.8, classification half** (paper (18); statement moved from
`GQ2/SectionThree.lean`, see the pointer there).  Every continuous `χ₀`-preserving automorphism
`ξ` of `B = D₀^{ab}` is `α_{u,b}` for a **unique** `(u, b) ∈ ℤ₂ˣ × ℤ₂`: in the coordinates of
the `B`-decomposition it sends `S̄ ↦ S̄^u`, `Ȳ ↦ S̄^b Ȳ`, and (forced by preservation of the
torsion element `t = Ā S̄²` and the relation `Ā² S̄⁴ = 1`) `Ā ↦ t S̄^{-2u}`.  The `S̄`-exponent
`u` is a unit because the same row analysis applies to `ξ⁻¹`.  Axiom-free: the abelianized `D₀`
and its coordinate frame are concrete. -/
theorem prop_3_8_classification
    (χ : topAbelianization (D0 : Type) →* ℤ_[2]ˣ) (hχ : Continuous χ)
    (hχA : χ (abMk d0A) = -1)
    (hχS : χ (abMk d0S) = 1)
    (hχY : ∀ y : ℤ_[2]ˣ, (y : ℤ_[2]) = -3 → χ (abMk d0Y) = y⁻¹)
    (hpres : ∀ x, χ (ξ x) = χ x) :
    ∃! p : ℤ_[2]ˣ × ℤ_[2],
      B.e (ξ (abMk d0A)) = Multiplicative.ofAdd (1, -2 * (p.1 : ℤ_[2]), 0) ∧
      B.e (ξ (abMk d0S)) = Multiplicative.ofAdd (0, (p.1 : ℤ_[2]), 0) ∧
      B.e (ξ (abMk d0Y)) = Multiplicative.ofAdd (0, p.2, 1) := by
  obtain ⟨y₀, hy₀⟩ : ∃ y₀ : ℤ_[2]ˣ, (y₀ : ℤ_[2]) = -3 :=
    ⟨(isUnit_intCast_of_odd (⟨-2, by ring⟩ : Odd (-3 : ℤ))).unit, by
      rw [IsUnit.unit_spec]
      push_cast
      ring⟩
  have hχY' : χ (abMk d0Y) = y₀⁻¹ := hχY y₀ hy₀
  obtain ⟨uval, huS⟩ := xi_S_row ξ χ hχ y₀ hy₀ hχA hχS hχY' hpres
  obtain ⟨b, hbY⟩ := xi_Y_row ξ χ hχ y₀ hy₀ hχA hχS hχY' hpres
  -- the `S̄`-exponent is a unit: the same row extraction for `ξ⁻¹` provides the cofactor
  have hpres' : ∀ x, χ (ξ.symm x) = χ x := fun x => by
    have h := hpres (ξ.symm x)
    rw [ContinuousMulEquiv.apply_symm_apply] at h
    exact h.symm
  obtain ⟨u', huS'⟩ := xi_S_row ξ.symm χ hχ y₀ hy₀ hχA hχS hχY' hpres'
  have hcomp : (abMk d0S : topAbelianization (D0 : Type)) = sBar (uval * u') := by
    have h1 : (abMk d0S : topAbelianization (D0 : Type)) = ξ (ξ.symm (abMk d0S)) :=
      (ξ.apply_symm_apply _).symm
    rw [huS', sBar, xi_zpow ξ, huS, sBar, zpowZtwo_zpowZtwo] at h1
    exact h1
  have hunit : IsUnit uval := by
    have hone : sBar (1 : ℤ_[2]) = abMk d0S := by rw [sBar, zpowZtwo_one_exp]
    have h1 : (1 : ℤ_[2]) = uval * u' := sBar_injective B (hone.trans hcomp)
    exact IsUnit.of_mul_eq_one u' h1.symm
  obtain ⟨u, hu⟩ : ∃ u : ℤ_[2]ˣ, (u : ℤ_[2]) = uval := ⟨hunit.unit, hunit.unit_spec⟩
  -- the three rows in `B.e`-coordinates
  have hSrow : B.e (ξ (abMk d0S)) = ofAdd ((0 : ZMod 2), uval, (0 : ℤ_[2])) := by
    rw [huS]
    exact bE_sBar B uval
  have hYrow : B.e (ξ (abMk d0Y)) = ofAdd ((0 : ZMod 2), b, (1 : ℤ_[2])) := by
    rw [hbY, map_mul, bE_sBar B, B.map_Y, ← ofAdd_add]
    refine congrArg ofAdd (Prod.ext ?_ (Prod.ext ?_ ?_))
    · show (0 : ZMod 2) + 0 = 0
      decide
    · show b + 0 = b
      ring
    · show (0 : ℤ_[2]) + 1 = 1
      ring
  have hArow : B.e (ξ (abMk d0A)) = ofAdd ((1 : ZMod 2), -2 * uval, (0 : ℤ_[2])) := by
    have hAdec : (abMk d0A : topAbelianization (D0 : Type))
        = abMk (d0A * d0S ^ 2) * ((abMk d0S) ^ 2)⁻¹ := by
      rw [map_mul, map_pow, mul_inv_cancel_right]
    have hξA : ξ (abMk d0A) = abMk (d0A * d0S ^ 2) * ((sBar uval) ^ 2)⁻¹ := by
      rw [hAdec, map_mul, map_inv, map_pow, xi_fixes_t B ξ, huS]
    rw [hξA, map_mul, map_inv, map_pow, B.map_t, bE_sBar B, pow_two, ← ofAdd_add,
      ← ofAdd_neg, ← ofAdd_add]
    refine congrArg ofAdd (Prod.ext ?_ (Prod.ext ?_ ?_))
    · show (1 : ZMod 2) + -((0 : ZMod 2) + 0) = 1
      decide
    · show (0 : ℤ_[2]) + -(uval + uval) = -2 * uval
      ring
    · show (0 : ℤ_[2]) + -((0 : ℤ_[2]) + 0) = 0
      ring
  refine ⟨(u, b), ⟨?_, ?_, ?_⟩, ?_⟩
  · show B.e (ξ (abMk d0A)) = ofAdd ((1 : ZMod 2), -2 * (u : ℤ_[2]), (0 : ℤ_[2]))
    rw [hu]
    exact hArow
  · show B.e (ξ (abMk d0S)) = ofAdd ((0 : ZMod 2), (u : ℤ_[2]), (0 : ℤ_[2]))
    rw [hu]
    exact hSrow
  · exact hYrow
  · rintro ⟨v, c⟩ ⟨-, hvS, hvY⟩
    have hv : (v : ℤ_[2]) = uval := by
      have h := hvS.symm.trans hSrow
      exact congrArg (fun z => (Multiplicative.toAdd z).2.1) h
    have hc : c = b := by
      have h := hvY.symm.trans hYrow
      exact congrArg (fun z => (Multiplicative.toAdd z).2.1) h
    refine Prod.ext ?_ ?_
    · show v = u
      refine Units.ext ?_
      rw [hu]
      exact hv
    · exact hc

end SectionThree

end ClassificationHalf

end GQ2
