import GQ2.KummerFiltration
import GQ2.HomCounting

/-!
# Counting admissible families via the equivariant-Hom engine  (ticket P-15f6, brick iii)

The bridge identifying `LocalKummer.AdmissibleFam ρ` with the equivariant Homs
`equivHoms C (V →+ 𝔽₂) (H¹(N, 𝔽₂))` (the acting group `C = H_V`; `H¹(N)` carries the
`conjModule` action from brick ii, `V^∨` the dual action `dualModule`), so that the P-15f5
counting engine applies to the `U_{e+1}` filtration.

* `dualModule` — the dual `C`-action on `V^∨ = V →+ 𝔽₂`, `(c • φ) v = φ (c⁻¹ • v)`.

WIP (this file is under construction for brick iii).
-/

namespace GQ2

open ContCoh LocalKummer

local notation "ℚ̄₂" => AlgebraicClosure ℚ_[2]

/-- **`deepClasses` as an additive subgroup** of `H¹(N, 𝔽₂)`: the deep Kummer classes are closed
under `0`/`+`/`neg` — deep units form a group (`A₁A₂` deep), `[a] + [b] = [ab]` via
`kcf_mul_of_fixed`, and `H¹` is 2-torsion so `neg = id`.  The subgroup form the `U_{e+1}` short
exact sequence (P-15f6 brick iii-b) and f2's orbit analysis consume. -/
noncomputable def deepClassesSubgroup (N : Subgroup (Kummer.GaloisGroup ℚ_[2])) :
    AddSubgroup (H1 ↥N (ZMod 2)) where
  carrier := deepClasses N
  zero_mem' := by
    refine ⟨1, 1, ⟨one_ne_zero, fun g _ => by rw [AlgEquiv.smul_def, map_one], 0,
      fun g _ => smul_zero g, by ring, by rw [norm_zero]; exact zero_lt_one⟩,
      one_pow 2, one_ne_zero, ?_⟩
    have hk1 : (fun n : ↥N => Kummer.kummerCocycleFun (1 : ℚ̄₂)
        ((n : Kummer.GaloisGroup ℚ_[2]))) = 0 := by
      funext n
      exact Kummer.kummerCocycleFun_eq0 (by rw [AlgEquiv.smul_def, map_one])
    rw [hk1, H1ofFun_of_mem (zero_mem _)]
    exact map_zero (H1mk ↥N (ZMod 2))
  add_mem' := by
    rintro ξ η ⟨A₁, β₁, hd₁, hsq₁, hne₁, rfl⟩ ⟨A₂, β₂, hd₂, hsq₂, hne₂, rfl⟩
    obtain ⟨hA₁0, hA₁fix, b₁, hb₁fix, hA₁eq, hb₁⟩ := hd₁
    obtain ⟨hA₂0, hA₂fix, b₂, hb₂fix, hA₂eq, hb₂⟩ := hd₂
    have h2le : ‖(2 : ℚ̄₂)‖ ≤ 1 := by
      rw [show (2 : ℚ̄₂) = 1 + 1 by norm_num]
      exact (IsUltrametricDist.norm_add_le_max 1 1).trans (by rw [norm_one, max_self])
    refine ⟨A₁ * A₂, β₁ * β₂,
      ⟨mul_ne_zero hA₁0 hA₂0, fun g hg => ?_, b₁ + b₂ + 2 * b₁ * b₂, fun g hg => ?_,
        by rw [hA₁eq, hA₂eq]; ring, ?_⟩,
      by rw [mul_pow, hsq₁, hsq₂], mul_ne_zero hne₁ hne₂, ?_⟩
    · rw [AlgEquiv.smul_def, map_mul, ← AlgEquiv.smul_def, ← AlgEquiv.smul_def,
        hA₁fix g hg, hA₂fix g hg]
    · rw [AlgEquiv.smul_def, map_add, map_add, map_mul, map_mul, map_ofNat,
        ← AlgEquiv.smul_def, ← AlgEquiv.smul_def, hb₁fix g hg, hb₂fix g hg]
    · have hprod : ‖(2 : ℚ̄₂) * b₁ * b₂‖ < 1 := by
        rw [norm_mul, norm_mul]
        calc ‖(2 : ℚ̄₂)‖ * ‖b₁‖ * ‖b₂‖
            ≤ 1 * ‖b₁‖ * ‖b₂‖ := by
              have := mul_le_mul_of_nonneg_right
                (mul_le_mul_of_nonneg_right h2le (norm_nonneg b₁)) (norm_nonneg b₂)
              simpa using this
          _ = ‖b₁‖ * ‖b₂‖ := by ring
          _ ≤ ‖b₁‖ * 1 := mul_le_mul_of_nonneg_left hb₂.le (norm_nonneg b₁)
          _ = ‖b₁‖ := mul_one _
          _ < 1 := hb₁
      refine lt_of_le_of_lt (IsUltrametricDist.norm_add_le_max _ _) ?_
      rw [max_lt_iff]
      exact ⟨lt_of_le_of_lt (IsUltrametricDist.norm_add_le_max _ _)
        (by rw [max_lt_iff]; exact ⟨hb₁, hb₂⟩), hprod⟩
    · have hLHS : (fun n : ↥N => Kummer.kummerCocycleFun (β₁ * β₂)
          ((n : Kummer.GaloisGroup ℚ_[2])))
          = (fun n : ↥N => Kummer.kummerCocycleFun β₁ ((n : Kummer.GaloisGroup ℚ_[2])))
            + fun n : ↥N => Kummer.kummerCocycleFun β₂ ((n : Kummer.GaloisGroup ℚ_[2])) := by
        funext n
        exact kcf_mul_of_fixed (by rw [mul_pow, hsq₁, hsq₂]) hsq₁ hsq₂ hne₁ hne₂
          (hA₁fix (n : Kummer.GaloisGroup ℚ_[2]) n.2) (hA₂fix (n : Kummer.GaloisGroup ℚ_[2]) n.2)
      rw [hLHS, GQ2.DeepPart.H1ofFun_add (GQ2.DeepPart.kummerRestrict_mem_Z1 hsq₁ hne₁ hA₁fix)
        (GQ2.DeepPart.kummerRestrict_mem_Z1 hsq₂ hne₂ hA₂fix)]
  neg_mem' := by
    intro ξ hξ
    rwa [neg_eq_of_add_eq_zero_left (GQ2.h1_add_self ξ)]

/-- The Kummer cocycle conjugates as `κ_β(g⁻¹ n g) = κ_{g·β}(n)` (the class of the conjugated
root).  Underlies the `conjModule`-invariance of `deepClasses`. -/
theorem kcf_conj (β : ℚ̄₂) (g n : Kummer.GaloisGroup ℚ_[2]) :
    Kummer.kummerCocycleFun β (g⁻¹ * n * g) = Kummer.kummerCocycleFun (g • β) n := by
  classical
  simp only [Kummer.kummerCocycleFun]
  refine if_congr ?_ rfl rfl
  rw [show g⁻¹ * n * g = g⁻¹ * (n * g) by group, mul_smul, mul_smul]
  exact inv_smul_eq_iff

variable {C : Type} [Group C] [TopologicalSpace C] [DiscreteTopology C] [Finite C]
variable {V : Type} [AddCommGroup V] [TopologicalSpace V] [DiscreteTopology V] [Finite V]
  [DistribMulAction AbsGalQ2 V] [ContinuousSMul AbsGalQ2 V] [DistribMulAction C V]

/-- The **dual `C`-action** on `V^∨ = V →+ 𝔽₂`: `(c • φ) v = φ (c⁻¹ • v)` (precomposition with
the inverse action on `V`).  Provided as a `def` (not a global instance — it competes with the
trivial codomain action on `V →+ 𝔽₂`); consumers `letI` it. -/
@[reducible] noncomputable def dualModule : DistribMulAction C (V →+ ZMod 2) where
  smul c φ := φ.comp (DistribSMul.toAddMonoidHom V c⁻¹)
  one_smul φ := by
    ext v
    show φ ((1 : C)⁻¹ • v) = φ v
    rw [inv_one, one_smul]
  mul_smul c d φ := by
    ext v
    show φ ((c * d)⁻¹ • v) = φ (d⁻¹ • c⁻¹ • v)
    rw [mul_inv_rev, mul_smul]
  smul_zero c := by ext v; rfl
  smul_add c φ ψ := by ext v; rfl

omit [TopologicalSpace C] [DiscreteTopology C] [Finite C] [TopologicalSpace V]
  [DiscreteTopology V] [Finite V] [DistribMulAction AbsGalQ2 V] [ContinuousSMul AbsGalQ2 V] in
/-- Evaluation rule for `dualModule`. -/
theorem dualModule_smul_apply (c : C) (φ : V →+ ZMod 2) (v : V) :
    (dualModule.toSMul.smul c φ) v = φ (c⁻¹ • v) := rfl

variable (ρ : ContinuousMonoidHom AbsGalQ2 C)

omit [DiscreteTopology C] [Finite C] in
/-- **`conjModule`-invariance of `deepClasses`** (P-15f6 brick iii-b — the §4-handoff gate):
the `G_ℚ₂`-conjugation `conjAct ρ g` carries a deep Kummer class to a deep Kummer class.
Concretely `conjAct ρ g [κ_β] = [κ_{g•β}]` (via `conjAct_h1ofFun` + `kcf_conj`), and `g • A` is
again a deep unit: normality of `ker ρ` keeps it `N`-fixed, and `‖g • b‖ = ‖b‖` by
`GQ2.norm_galois`.  This is the invariance that lets `deepClassesSubgroup` carry the restricted
`conjModule` action (f5's `W'`). -/
theorem conjAct_deepClasses (g : Kummer.GaloisGroup ℚ_[2])
    {ξ : H1 ↥(ρ.toMonoidHom.ker : Subgroup AbsGalQ2) (ZMod 2)}
    (hξ : ξ ∈ deepClasses (ρ.toMonoidHom.ker : Subgroup AbsGalQ2)) :
    conjAct ρ g ξ ∈ deepClasses (ρ.toMonoidHom.ker : Subgroup AbsGalQ2) := by
  obtain ⟨A, β, hdeep, hsq, hβ0, rfl⟩ := hξ
  obtain ⟨hA0, hAfix, b, hbfix, hAeq, hb⟩ := hdeep
  -- `g` is taken in the reducible `GaloisGroup` view so the field action `g • ·` on `ℚ̄₂`
  -- synthesizes (handoff §4, HSMul half); `conjAct ρ g` / `conj_mem_ker ρ g` still accept it by
  -- defeq (they expect `AbsGalQ2`).  Build the deep-class witness FIRST (elaborated at `.default`
  -- transparency, where the two `Group` instances are defeq); the `conjAct_h1ofFun` rewrite is
  -- then done on the final plain `H1`-equation goal, never under `∈ deepClasses` (which would
  -- force the `AlgEquiv.aut` view and break the `rw` motive).
  refine ⟨g • A, g • β, ⟨?_, ?_, g • b, ?_, ?_, ?_⟩, ?_, ?_, ?_⟩
  · rw [AlgEquiv.smul_def]; simpa using hA0
  · intro m hm
    have hconj : (g⁻¹ * m * g) • A = A :=
      hAfix _ (conj_mem_ker ρ g ⟨m, hm⟩)
    calc m • (g • A) = g • ((g⁻¹ * m * g) • A) := by
          rw [← mul_smul, ← mul_smul]; congr 1; group
      _ = g • A := by rw [hconj]
  · intro m hm
    have hconj : (g⁻¹ * m * g) • b = b :=
      hbfix _ (conj_mem_ker ρ g ⟨m, hm⟩)
    calc m • (g • b) = g • ((g⁻¹ * m * g) • b) := by
          rw [← mul_smul, ← mul_smul]; congr 1; group
      _ = g • b := by rw [hconj]
  · rw [hAeq, AlgEquiv.smul_def, map_add, map_one, map_mul, map_ofNat, ← AlgEquiv.smul_def]
  · rw [norm_galois]; exact hb
  · rw [AlgEquiv.smul_def, AlgEquiv.smul_def, ← map_pow, hsq]
  · rw [AlgEquiv.smul_def]; simpa using hβ0
  · -- `H1ofFun (κ_{g•β}) = conjAct ρ g (H1ofFun κ_β)`.  `conjAct ρ g` wants `g : AbsGalQ2` while
    -- the field action `g • β` wants `g : GaloisGroup`; a single `rw` on `conjAct ρ g` cannot
    -- satisfy both under the `instances`-transparency motive check.  So we go through a `calc`
    -- (pure `Eq.trans`, no motive over the goal): the `conjAct_h1ofFun` step is a plain equation
    -- term, and the final equality is checked by defeq.
    symm
    calc conjAct ρ g (H1ofFun ↥(ρ.toMonoidHom.ker : Subgroup AbsGalQ2)
            (fun n => Kummer.kummerCocycleFun β (n : AbsGalQ2)))
        = H1ofFun ↥(ρ.toMonoidHom.ker : Subgroup AbsGalQ2)
            (fun n => Kummer.kummerCocycleFun β ((conjMap ρ g n : AbsGalQ2))) :=
          conjAct_h1ofFun ρ g (GQ2.DeepPart.kummerRestrict_mem_Z1 hsq hβ0 hAfix)
      _ = H1ofFun ↥(ρ.toMonoidHom.ker : Subgroup AbsGalQ2)
            (fun n => Kummer.kummerCocycleFun (g • β) (n : AbsGalQ2)) := by
          congr 1; funext n; exact kcf_conj β g (n : AbsGalQ2)

/-- `conjAct ρ g` packaged as an additive endomorphism of `H¹(N, 𝔽₂)` (`conjAct_add`), so it can
feed `QuotientAddGroup.map` for the induced action on `H¹(N) ⧸ deepClassesSubgroup`. -/
noncomputable def conjActHom (g : AbsGalQ2) :
    H1 ↥(ρ.toMonoidHom.ker : Subgroup AbsGalQ2) (ZMod 2) →+
      H1 ↥(ρ.toMonoidHom.ker : Subgroup AbsGalQ2) (ZMod 2) :=
  AddMonoidHom.mk' (conjAct ρ g) (conjAct_add ρ g)

/-- **The restricted `conjModule` action on the deep subgroup** (f5's `W'`): `deepClassesSubgroup`
is `conjModule`-invariant (`conjAct_deepClasses`), so the conjugation action restricts to a
`DistribMulAction C` on `↥(deepClassesSubgroup (ker ρ))`.  Provided as a `@[reducible]` `def`
(like `conjModule`); consumers `letI` it. -/
@[reducible] noncomputable def conjModuleDeep (hρsurj : Function.Surjective ⇑ρ) :
    DistribMulAction C ↥(deepClassesSubgroup (ρ.toMonoidHom.ker : Subgroup AbsGalQ2)) where
  smul c ξ := ⟨conjAct ρ (Function.surjInv hρsurj c) ξ.1,
    conjAct_deepClasses ρ (Function.surjInv hρsurj c) ξ.2⟩
  one_smul ξ := by
    apply Subtype.ext
    show conjAct ρ (Function.surjInv hρsurj 1) ξ.1 = ξ.1
    refine (conjAct_ker ρ _ 1 ?_ ξ.1).trans (conjAct_one ρ ξ.1)
    rw [Function.surjInv_eq hρsurj, map_one]
  mul_smul c d ξ := by
    apply Subtype.ext
    show conjAct ρ (Function.surjInv hρsurj (c * d)) ξ.1
      = conjAct ρ (Function.surjInv hρsurj c) (conjAct ρ (Function.surjInv hρsurj d) ξ.1)
    rw [← conjAct_comp]
    refine conjAct_ker ρ _ _ ?_ ξ.1
    rw [map_mul, Function.surjInv_eq hρsurj, Function.surjInv_eq hρsurj,
      Function.surjInv_eq hρsurj]
  smul_zero c := by
    apply Subtype.ext; exact conjAct_zero ρ (Function.surjInv hρsurj c)
  smul_add c ξ η := by
    apply Subtype.ext; exact conjAct_add ρ (Function.surjInv hρsurj c) ξ.1 η.1

/-- The descent of `conjAct ρ g` to `H¹(N) ⧸ deepClassesSubgroup`, via `QuotientAddGroup.map`
(well-defined because `deepClassesSubgroup` is `conjAct`-invariant, `conjAct_deepClasses`). -/
noncomputable def conjActQuotHom (g : AbsGalQ2) :
    (H1 ↥(ρ.toMonoidHom.ker : Subgroup AbsGalQ2) (ZMod 2) ⧸
        deepClassesSubgroup (ρ.toMonoidHom.ker : Subgroup AbsGalQ2)) →+
      (H1 ↥(ρ.toMonoidHom.ker : Subgroup AbsGalQ2) (ZMod 2) ⧸
        deepClassesSubgroup (ρ.toMonoidHom.ker : Subgroup AbsGalQ2)) :=
  QuotientAddGroup.map (deepClassesSubgroup (ρ.toMonoidHom.ker : Subgroup AbsGalQ2))
    (deepClassesSubgroup (ρ.toMonoidHom.ker : Subgroup AbsGalQ2)) (conjActHom ρ g)
    (by intro x hx; exact AddSubgroup.mem_comap.mpr (conjAct_deepClasses ρ g hx))

omit [DiscreteTopology C] [Finite C] in
/-- Computation rule for `conjActQuotHom` on a class. -/
theorem conjActQuotHom_mk (g : AbsGalQ2)
    (a : H1 ↥(ρ.toMonoidHom.ker : Subgroup AbsGalQ2) (ZMod 2)) :
    conjActQuotHom ρ g (QuotientAddGroup.mk a) = QuotientAddGroup.mk (conjAct ρ g a) :=
  QuotientAddGroup.map_mk _ _ (conjActHom ρ g) _ a

/-- **The induced `conjModule` action on the quotient** (f5's `W''`): since `deepClassesSubgroup`
is `conjModule`-invariant, the conjugation action descends to `H¹(N) ⧸ deepClassesSubgroup` via
`conjActQuotHom`.  Provided as a `@[reducible]` `def`; consumers `letI` it. -/
@[reducible] noncomputable def conjModuleQuot (hρsurj : Function.Surjective ⇑ρ) :
    DistribMulAction C (H1 ↥(ρ.toMonoidHom.ker : Subgroup AbsGalQ2) (ZMod 2) ⧸
        deepClassesSubgroup (ρ.toMonoidHom.ker : Subgroup AbsGalQ2)) where
  smul c x := conjActQuotHom ρ (Function.surjInv hρsurj c) x
  one_smul x := by
    refine QuotientAddGroup.induction_on x (fun a => ?_)
    show conjActQuotHom ρ (Function.surjInv hρsurj 1) (QuotientAddGroup.mk a) = QuotientAddGroup.mk a
    rw [conjActQuotHom_mk]
    congr 1
    refine (conjAct_ker ρ _ 1 ?_ a).trans (conjAct_one ρ a)
    rw [Function.surjInv_eq hρsurj, map_one]
  mul_smul c d x := by
    refine QuotientAddGroup.induction_on x (fun a => ?_)
    show conjActQuotHom ρ (Function.surjInv hρsurj (c * d)) (QuotientAddGroup.mk a)
      = conjActQuotHom ρ (Function.surjInv hρsurj c)
          (conjActQuotHom ρ (Function.surjInv hρsurj d) (QuotientAddGroup.mk a))
    simp only [conjActQuotHom_mk]
    congr 1
    show conjAct ρ (Function.surjInv hρsurj (c * d)) a
      = conjAct ρ (Function.surjInv hρsurj c) (conjAct ρ (Function.surjInv hρsurj d) a)
    rw [← conjAct_comp]
    refine conjAct_ker ρ _ _ ?_ a
    rw [map_mul, Function.surjInv_eq hρsurj, Function.surjInv_eq hρsurj,
      Function.surjInv_eq hρsurj]
  smul_zero c := map_zero _
  smul_add c x y := map_add _ x y

omit [DiscreteTopology C] [Finite C] [TopologicalSpace V] [DiscreteTopology V] [Finite V]
  [ContinuousSMul AbsGalQ2 V] in
/-- **The core equivariance of an admissible family** matching the two `C`-actions: `ξ.fam`
intertwines the dual action `dualModule` on `V^∨` with the conjugation action `conjModule` on
`H¹(N)`.  The `AdmissibleFam.equiv'` field is stated in the `G_ℚ₂`-conjugation form; this
converts it to the `C`-form via a lift `surjInv c` and `hρ` (the `G_ℚ₂`/`C` action
compatibility on `V`). -/
theorem fam_equivariant (hρ : ∀ (g : AbsGalQ2) (v : V), g • v = ρ g • v)
    (hρsurj : Function.Surjective ⇑ρ) (ξ : AdmissibleFam (V := V) ρ) (c : C)
    (φ : V →+ ZMod 2) :
    ξ.fam (φ.comp (DistribSMul.toAddMonoidHom V (c⁻¹ : C)))
      = conjAct ρ (Function.surjInv hρsurj c) (ξ.fam φ) := by
  rw [ξ.equiv' (Function.surjInv hρsurj c) φ]
  refine congrArg ξ.fam (AddMonoidHom.ext fun v => ?_)
  show φ ((c⁻¹ : C) • v) = φ ((Function.surjInv hρsurj c)⁻¹ • v)
  rw [hρ (Function.surjInv hρsurj c)⁻¹ v, map_inv, Function.surjInv_eq hρsurj]

/-- **The bridge `AdmissibleFam ≃ equivHoms`** (brick iii): admissible families are exactly the
`C`-equivariant additive maps `V^∨ → H¹(N)`, under the dual action `dualModule` on `V^∨` and the
`conjModule` conjugation action on `H¹(N)`.  Forward equivariance is `fam_equivariant`; the
converse re-derives `equiv'` from `C`-equivariance at `c = ρ g` (via `conjAct_ker` + `hρ`). -/
noncomputable def admissibleFamEquiv
    (hρ : ∀ (g : AbsGalQ2) (v : V), g • v = ρ g • v) (hρsurj : Function.Surjective ⇑ρ) :
    letI := conjModule ρ hρsurj
    letI : DistribMulAction C (V →+ ZMod 2) := dualModule
    AdmissibleFam (V := V) ρ ≃ equivHoms C (V →+ ZMod 2)
      (H1 ↥(ρ.toMonoidHom.ker : Subgroup AbsGalQ2) (ZMod 2)) :=
  letI := conjModule ρ hρsurj
  letI : DistribMulAction C (V →+ ZMod 2) := dualModule
  { toFun := fun ξ => ⟨AddMonoidHom.mk' ξ.fam ξ.add',
      fun c φ => fam_equivariant ρ hρ hρsurj ξ c φ⟩
    invFun := fun f =>
      { fam := f.1
        add' := map_add f.1
        equiv' := fun g φ => by
          calc conjAct ρ g (f.1 φ)
              = conjAct ρ (Function.surjInv hρsurj (ρ g)) (f.1 φ) :=
                conjAct_ker ρ g (Function.surjInv hρsurj (ρ g))
                  (Function.surjInv_eq hρsurj (ρ g)).symm (f.1 φ)
            _ = (dualModule.toSMul.smul (ρ g) φ |> f.1) := (f.2 (ρ g) φ).symm
            _ = f.1 (φ.comp (DistribSMul.toAddMonoidHom V g⁻¹)) :=
                congrArg f.1 (AddMonoidHom.ext fun v => by
                  show φ ((ρ g)⁻¹ • v) = φ (g⁻¹ • v)
                  rw [hρ g⁻¹ v, map_inv]) }
    left_inv := fun ξ => rfl
    right_inv := fun f => Subtype.ext (AddMonoidHom.ext fun φ => rfl) }

omit [DiscreteTopology C] [Finite C] [TopologicalSpace V] [DiscreteTopology V] [Finite V]
  [ContinuousSMul AbsGalQ2 V] in
/-- **Count admissible families as equivariant Homs**: `#AdmissibleFam = #equivHoms C V^∨ H¹(N)`.
This lets the P-15f5 engine (`card_equivHoms_of_exact`) count `AdmissibleFam` across the
`U_{e+1}` filtration of `H¹(N) ≅ M_K`. -/
theorem card_admissibleFam_eq (hρ : ∀ (g : AbsGalQ2) (v : V), g • v = ρ g • v)
    (hρsurj : Function.Surjective ⇑ρ) :
    letI := conjModule ρ hρsurj
    letI : DistribMulAction C (V →+ ZMod 2) := dualModule
    Nat.card (AdmissibleFam (V := V) ρ)
      = Nat.card ↥(equivHoms C (V →+ ZMod 2)
          (H1 ↥(ρ.toMonoidHom.ker : Subgroup AbsGalQ2) (ZMod 2))) :=
  letI := conjModule ρ hρsurj
  letI : DistribMulAction C (V →+ ZMod 2) := dualModule
  Nat.card_congr (admissibleFamEquiv ρ hρ hρsurj)

/-- **The deep-families bridge** (P-15f6 step 4): the admissible families valued in the deep
classes are exactly the `C`-equivariant maps `V^∨ → deepClassesSubgroup` (under `dualModule` on
`V^∨` and the restricted `conjModuleDeep` on the deep subgroup).  Mirrors `admissibleFamEquiv`,
restricted through `deepClassesSubgroup`. -/
noncomputable def deepFamEquiv
    (hρ : ∀ (g : AbsGalQ2) (v : V), g • v = ρ g • v) (hρsurj : Function.Surjective ⇑ρ) :
    letI := conjModuleDeep ρ hρsurj
    letI : DistribMulAction C (V →+ ZMod 2) := dualModule
    {ξ : AdmissibleFam (V := V) ρ // ∀ φ : V →+ ZMod 2,
        ξ.fam φ ∈ deepClasses (ρ.toMonoidHom.ker : Subgroup AbsGalQ2)}
      ≃ equivHoms C (V →+ ZMod 2)
          ↥(deepClassesSubgroup (ρ.toMonoidHom.ker : Subgroup AbsGalQ2)) :=
  letI := conjModuleDeep ρ hρsurj
  letI : DistribMulAction C (V →+ ZMod 2) := dualModule
  { toFun := fun ξ => ⟨AddMonoidHom.mk' (fun φ => ⟨ξ.1.fam φ, ξ.2 φ⟩)
      (fun φ ψ => by apply Subtype.ext; exact ξ.1.add' φ ψ),
      fun c φ => by apply Subtype.ext; exact fam_equivariant ρ hρ hρsurj ξ.1 c φ⟩
    invFun := fun f =>
      ⟨{ fam := fun φ => (f.1 φ).1
         add' := fun φ ψ => by rw [map_add]; rfl
         equiv' := fun g φ => by
           calc conjAct ρ g ((f.1 φ).1)
               = conjAct ρ (Function.surjInv hρsurj (ρ g)) (f.1 φ).1 :=
                 conjAct_ker ρ g (Function.surjInv hρsurj (ρ g))
                   (Function.surjInv_eq hρsurj (ρ g)).symm (f.1 φ).1
             _ = ((dualModule.toSMul.smul (ρ g) φ |> f.1) : ↥(deepClassesSubgroup _)).1 :=
                 (congrArg Subtype.val (f.2 (ρ g) φ)).symm
             _ = (f.1 (φ.comp (DistribSMul.toAddMonoidHom V g⁻¹))).1 :=
                 congrArg (fun ψ => (f.1 ψ).1) (AddMonoidHom.ext fun v => by
                   show φ ((ρ g)⁻¹ • v) = φ (g⁻¹ • v)
                   rw [hρ g⁻¹ v, map_inv]) },
       fun φ => (f.1 φ).2⟩
    left_inv := fun ξ => rfl
    right_inv := fun f => Subtype.ext (AddMonoidHom.ext fun φ => Subtype.ext rfl) }

omit [DiscreteTopology C] [Finite C] [TopologicalSpace V] [DiscreteTopology V] [Finite V]
  [ContinuousSMul AbsGalQ2 V] in
/-- **Count the deep families as equivariant Homs into the deep subgroup**:
`#{deep families} = #equivHoms C V^∨ deepClassesSubgroup` (P-15f6 step 4). -/
theorem card_deepFam_eq (hρ : ∀ (g : AbsGalQ2) (v : V), g • v = ρ g • v)
    (hρsurj : Function.Surjective ⇑ρ) :
    letI := conjModuleDeep ρ hρsurj
    letI : DistribMulAction C (V →+ ZMod 2) := dualModule
    Nat.card {ξ : AdmissibleFam (V := V) ρ // ∀ φ : V →+ ZMod 2,
        ξ.fam φ ∈ deepClasses (ρ.toMonoidHom.ker : Subgroup AbsGalQ2)}
      = Nat.card ↥(equivHoms C (V →+ ZMod 2)
          ↥(deepClassesSubgroup (ρ.toMonoidHom.ker : Subgroup AbsGalQ2))) :=
  letI := conjModuleDeep ρ hρsurj
  letI : DistribMulAction C (V →+ ZMod 2) := dualModule
  Nat.card_congr (deepFamEquiv ρ hρ hρsurj)

/- **P-15f6 step 3 (the `U_{e+1}` SES count) is DEFERRED** — see `docs/p15f-handoff.md` §7.
The `card_equivHoms_of_exact` application to `0 → deepClassesSubgroup → H¹(N) → H¹(N)/deep → 0`
is structurally complete (`j = AddSubgroup.subtype`, `π = QuotientAddGroup.mk'`, `hjeq`/`hπeq`
hold by construction of `conjModuleDeep`/`conjModuleQuot`, `hexact` by `QuotientAddGroup.eq_zero_iff`
+ `AddSubgroup.range_subtype`), but is blocked by the `AbsGalQ2`/`GaloisGroup` view mismatch on
`deepClassesSubgroup ρ.ker`: the quotient's `.Normal` instance resolves at top level but NOT in the
nested position `card_equivHoms_of_exact` needs it (`instances`-transparency, per handoff §4).
Resolving it needs the standalone view-normalization brick flagged there. -/

end GQ2
