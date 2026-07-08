import GQ2.LocalKummer

/-!
# P-15f8 (increment 2): `FamiliesExtend` from the Lemma 6.11 package

`FamiliesExtend ρ` (`GQ2/LocalKummer.lean`) — every admissible family `V^∨ → H¹(N, 𝔽₂)` is the
scalar-restriction family of a class in `H¹(ℚ₂, V)` — is the `H²(H_V, V) = 0` input of the
`lemma_6_17_dim` chain (the paper's (78) projectivity logic).  This file **discharges it from
the Lemma 6.11 regular-summand package alone** (`familiesExtend_of_package`), with no counting
and no graded filtration:

1. **Inverse Shapiro at the free module.**  For the regular coefficients
   `RegMod C Nr` (`𝔽₂[C]^{Nr}` with the left-translation action, pulled back to `G_ℚ₂` through
   `ρ`), every admissible family extends.  The extension is the explicit coinduced-module
   cocycle `b(g)(n, x) := u_n(s(x)⁻¹ · g · s(ρ(g)⁻¹x))` where `s` is a normalized set-section
   of `ρ` and `u_n` represents the family's value at the evaluation functional `ev_{n,1}`; the
   cocycle identity is the middle-insertion factorization of the `shapiroWord`, and the family
   is recovered on all of `R^∨` from the single seed `ev_{n,1}` by conjugation-equivariance
   (`ρ` surjective) plus the finite `ev`-span of `R^∨`.
2. **Retract transfer.**  `phiRes` is natural in the coefficient module
   (`phiRes_mapCoeff1`), so along the package `(ι, r)` with `r ∘ ι = id` a family on `V` is
   pushed to `RegMod` (`ψ ↦ ξ(ψ ∘ ι)`), extended there, and the extending class is pulled back
   through `mapCoeff1 r` — `FamiliesExtend` for `V` itself.

`RegMod C Nr` is an **instance-opaque type synonym** (a plain `def`) for
`Fin Nr → C → ZMod 2`: the repo's global trivial action of `G_ℚ₂` on `ZMod 2`
(`GQ2/SectionSix.lean`) lifts pointwise over raw function types and would clash with the
translation action; the synonym hides the pi-shape from instance search, so the actions
declared here are the only candidates.  Everything here is `#print axioms` ⊆ std-3.

Consumer: `GQ2/DimAssembly.lean` (`lemma_6_17_dim_of_hduality`), which obtains the `V`-side
package from `lemma_6_11_of_tame_pair` and thereby removes `hext` from the `lemma_6_17_dim`
parameter list (leaving only P-15f7's `hduality`).
-/

open scoped Classical

namespace GQ2

namespace ShapiroExtend

open ContCoh LocalKummer

variable {C : Type} [Group C] [TopologicalSpace C] [DiscreteTopology C] [Finite C]

/-! ## The normalized section and the Shapiro word -/

/-- A set-theoretic section of `ρ`, normalized so that `sec1 ρ hρsurj 1 = 1`. -/
noncomputable def sec1 (ρ : ContinuousMonoidHom AbsGalQ2 C) (hρsurj : Function.Surjective ⇑ρ)
    (c : C) : AbsGalQ2 :=
  if c = 1 then 1 else Function.surjInv hρsurj c

omit [DiscreteTopology C] [Finite C] in
theorem sec1_spec (ρ : ContinuousMonoidHom AbsGalQ2 C) (hρsurj : Function.Surjective ⇑ρ)
    (c : C) : ρ (sec1 ρ hρsurj c) = c := by
  unfold sec1
  split_ifs with h
  · rw [h, map_one]
  · exact Function.surjInv_eq hρsurj c

omit [DiscreteTopology C] [Finite C] in
theorem sec1_one (ρ : ContinuousMonoidHom AbsGalQ2 C) (hρsurj : Function.Surjective ⇑ρ) :
    sec1 ρ hρsurj 1 = 1 := if_pos rfl

variable (ρ : ContinuousMonoidHom AbsGalQ2 C) (hρsurj : Function.Surjective ⇑ρ)

omit [DiscreteTopology C] [Finite C] in
/-- The Shapiro word `s(x)⁻¹ · g · s(ρ(g)⁻¹x)` lies in `N = ker ρ`. -/
theorem shapiroWord_mem (g : AbsGalQ2) (x : C) :
    (sec1 ρ hρsurj x)⁻¹ * g * sec1 ρ hρsurj ((ρ g)⁻¹ * x)
      ∈ (ρ.toMonoidHom.ker : Subgroup AbsGalQ2) := by
  show ρ ((sec1 ρ hρsurj x)⁻¹ * g * sec1 ρ hρsurj ((ρ g)⁻¹ * x)) = 1
  rw [map_mul, map_mul, map_inv, sec1_spec, sec1_spec]
  group

/-- The inverse-Shapiro word `s(x)⁻¹ · g · s(ρ(g)⁻¹x)`, as an element of `↥N`.  This is the
`(g, x)`-entry of the coinduced-module extension cocycle. -/
noncomputable def shapiroWord (g : AbsGalQ2) (x : C) :
    ↥(ρ.toMonoidHom.ker : Subgroup AbsGalQ2) :=
  ⟨(sec1 ρ hρsurj x)⁻¹ * g * sec1 ρ hρsurj ((ρ g)⁻¹ * x), shapiroWord_mem ρ hρsurj g x⟩

omit [DiscreteTopology C] [Finite C] in
/-- Middle-insertion factorization — the source of the cocycle identity for the extension. -/
theorem shapiroWord_mul (g h : AbsGalQ2) (x : C) :
    shapiroWord ρ hρsurj (g * h) x
      = shapiroWord ρ hρsurj g x * shapiroWord ρ hρsurj h ((ρ g)⁻¹ * x) := by
  apply Subtype.ext
  show (sec1 ρ hρsurj x)⁻¹ * (g * h) * sec1 ρ hρsurj ((ρ (g * h))⁻¹ * x)
    = ((sec1 ρ hρsurj x)⁻¹ * g * sec1 ρ hρsurj ((ρ g)⁻¹ * x))
      * ((sec1 ρ hρsurj ((ρ g)⁻¹ * x))⁻¹ * h * sec1 ρ hρsurj ((ρ h)⁻¹ * ((ρ g)⁻¹ * x)))
  have harg : (ρ (g * h))⁻¹ * x = (ρ h)⁻¹ * ((ρ g)⁻¹ * x) := by
    rw [map_mul, mul_inv_rev, mul_assoc]
  rw [harg]
  group

omit [DiscreteTopology C] [Finite C] in
/-- On the kernel, at the base point `x = 1`, the word is the element itself. -/
theorem shapiroWord_ker_one (n₀ : ↥(ρ.toMonoidHom.ker : Subgroup AbsGalQ2)) :
    shapiroWord ρ hρsurj (n₀ : AbsGalQ2) 1 = n₀ := by
  apply Subtype.ext
  show (sec1 ρ hρsurj 1)⁻¹ * (n₀ : AbsGalQ2) * sec1 ρ hρsurj ((ρ n₀)⁻¹ * 1) = (n₀ : AbsGalQ2)
  have h1 : ρ (n₀ : AbsGalQ2) = 1 := n₀.2
  rw [h1, inv_one, one_mul, sec1_one, inv_one, one_mul, mul_one]

omit [Finite C] in
/-- Continuity of the word in `g` (the `C`-inputs are discrete, so the section legs are free). -/
theorem continuous_shapiroWord (x : C) :
    Continuous fun g : AbsGalQ2 => shapiroWord ρ hρsurj g x := by
  apply Continuous.subtype_mk
  have hsec : Continuous fun g : AbsGalQ2 => sec1 ρ hρsurj ((ρ g)⁻¹ * x) :=
    show Continuous ((fun c : C => sec1 ρ hρsurj (c⁻¹ * x)) ∘ ⇑ρ) from
      continuous_of_discreteTopology.comp ρ.continuous_toFun
  exact (continuous_const.mul continuous_id).mul hsec

/-! ## The regular coefficient module, instance-opaque -/

/-- The regular coefficients `𝔽₂[C]^{Nr}`, as an **instance-opaque** synonym of
`Fin Nr → C → ZMod 2`: a plain `def`, so the ambient pointwise-action instances on raw
function types (via the repo's global trivial `G_ℚ₂`-action on `ZMod 2`) cannot fire on it;
the left-translation `C`-action below is the unique action in scope. -/
def RegMod (C : Type) (Nr : ℕ) : Type := Fin Nr → C → ZMod 2

instance {α : Type} {Nr : ℕ} : AddCommGroup (RegMod α Nr) :=
  inferInstanceAs (AddCommGroup (Fin Nr → α → ZMod 2))

instance {α : Type} {Nr : ℕ} : TopologicalSpace (RegMod α Nr) :=
  inferInstanceAs (TopologicalSpace (Fin Nr → α → ZMod 2))

instance {α : Type} {Nr : ℕ} [Finite α] : DiscreteTopology (RegMod α Nr) :=
  inferInstanceAs (DiscreteTopology (Fin Nr → α → ZMod 2))

instance {α : Type} {Nr : ℕ} [Finite α] : Finite (RegMod α Nr) :=
  inferInstanceAs (Finite (Fin Nr → α → ZMod 2))

instance {α : Type} {Nr : ℕ} [Finite α] : IsTopologicalAddGroup (RegMod α Nr) where
  continuous_add := continuous_of_discreteTopology
  continuous_neg := continuous_of_discreteTopology

/-- The left-translation action of `C` on the regular coefficients. -/
instance {G' : Type} [Group G'] {Nr : ℕ} : DistribMulAction G' (RegMod G' Nr) where
  smul h F := fun n x => F n (h⁻¹ * x)
  one_smul F := by
    funext n x
    show F n (1⁻¹ * x) = F n x
    rw [inv_one, one_mul]
  mul_smul g h F := by
    funext n x
    show F n ((g * h)⁻¹ * x) = F n (h⁻¹ * (g⁻¹ * x))
    rw [mul_inv_rev, mul_assoc]
  smul_zero h := rfl
  smul_add h F G := rfl

/-! ## The evaluation span of the regular module's dual -/

section Span

variable (Nr : ℕ)

/-- The evaluation functional at `(n, x)` on the regular coefficients. -/
def evReg (n : Fin Nr) (x : C) : RegMod C Nr →+ ZMod 2 where
  toFun F := F n x
  map_zero' := rfl
  map_add' _ _ := rfl

omit [Group C] [TopologicalSpace C] [DiscreteTopology C] [Finite C] in
/-- **The `ev`-span**: every functional on the regular module is the (finite) sum of the
evaluations it supports — `R^∨` is spanned by the point evaluations. -/
theorem addHom_eq_sum_evReg [Fintype C] (φ : RegMod C Nr →+ ZMod 2) :
    φ = ∑ p ∈ Finset.univ.filter
        (fun p : Fin Nr × C => φ (Pi.single p.1 (Pi.single p.2 1)) = 1),
      evReg Nr p.1 p.2 := by
  have hz : ∀ z : ZMod 2, z = 0 ∨ z = 1 := by decide
  refine AddMonoidHom.ext fun F => ?_
  -- decompose the argument over the double basis of singles
  have hF1 : F = ∑ n, Pi.single n (F n) := (Finset.univ_sum_single F).symm
  have hF2 : ∀ n : Fin Nr, (Pi.single n (F n) : RegMod C Nr)
      = ∑ x, Pi.single n (Pi.single x (F n x)) := by
    intro n
    conv_lhs => rw [show F n = ∑ x, Pi.single x (F n x) from (Finset.univ_sum_single (F n)).symm]
    exact map_sum (AddMonoidHom.single (fun _ : Fin Nr => C → ZMod 2) n) _ Finset.univ
  -- the per-entry weighted-value identity, `𝔽₂`-cases
  have hentry : ∀ (n : Fin Nr) (x : C),
      φ (Pi.single n (Pi.single x (F n x))) = F n x * φ (Pi.single n (Pi.single x 1)) := by
    intro n x
    rcases hz (F n x) with h0 | h1
    · rw [h0, zero_mul, show Pi.single (M := fun _ => ZMod 2) x (0 : ZMod 2) = 0 from
        Pi.single_zero x, show Pi.single (M := fun _ => C → ZMod 2) n (0 : C → ZMod 2) = 0 from
        Pi.single_zero n]
      exact map_zero φ
    · rw [h1, one_mul]
  -- LHS: `φ F` as the double sum of weighted single-values
  have hlhs : φ F = ∑ n, ∑ x, F n x * φ (Pi.single n (Pi.single x 1)) :=
    calc φ F = φ (∑ n, Pi.single n (F n)) := congrArg φ hF1
      _ = ∑ n, φ (Pi.single n (F n)) := map_sum φ _ Finset.univ
      _ = ∑ n, φ (∑ x, Pi.single n (Pi.single x (F n x))) :=
          Finset.sum_congr rfl fun n _ => congrArg φ (hF2 n)
      _ = ∑ n, ∑ x, φ (Pi.single n (Pi.single x (F n x))) :=
          Finset.sum_congr rfl fun n _ => map_sum φ _ Finset.univ
      _ = ∑ n, ∑ x, F n x * φ (Pi.single n (Pi.single x 1)) :=
          Finset.sum_congr rfl fun n _ => Finset.sum_congr rfl fun x _ => hentry n x
  -- RHS: the filtered evaluation sum as the same double sum
  have hrhs : (∑ p ∈ Finset.univ.filter
        (fun p : Fin Nr × C => φ (Pi.single p.1 (Pi.single p.2 1)) = 1),
      evReg Nr p.1 p.2) F = ∑ n, ∑ x, F n x * φ (Pi.single n (Pi.single x 1)) := by
    rw [AddMonoidHom.finsetSum_apply]
    have hev : ∀ p : Fin Nr × C, evReg Nr p.1 p.2 F = F p.1 p.2 := fun _ => rfl
    rw [Finset.sum_congr rfl fun p _ => hev p, Finset.sum_filter, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun n _ => Finset.sum_congr rfl fun x _ => ?_
    show (if φ (Pi.single n (Pi.single x 1)) = 1 then F n x else 0)
      = F n x * φ (Pi.single n (Pi.single x 1))
    rcases hz (φ (Pi.single n (Pi.single x 1))) with h0 | h1
    · rw [h0, mul_zero, if_neg (show ¬(0 : ZMod 2) = 1 by decide)]
    · rw [h1, mul_one, if_pos rfl]
  rw [hlhs, hrhs]

end Span

/-! ## Naturality of the scalar restriction in the coefficient module -/

section Naturality

variable {W₁ W₂ : Type}
  [AddCommGroup W₁] [TopologicalSpace W₁] [DiscreteTopology W₁] [Finite W₁]
  [DistribMulAction AbsGalQ2 W₁] [ContinuousSMul AbsGalQ2 W₁] [DistribMulAction C W₁]
  [AddCommGroup W₂] [TopologicalSpace W₂] [DiscreteTopology W₂] [Finite W₂]
  [DistribMulAction AbsGalQ2 W₂] [ContinuousSMul AbsGalQ2 W₂] [DistribMulAction C W₂]
  [IsTopologicalAddGroup W₁] [IsTopologicalAddGroup W₂]

variable {ρ}

/-- **`phiRes` is natural in the coefficient module**: restricting a pushed-forward class is
pre-composing the functional.  The workhorse of the retract transfer. -/
theorem phiRes_mapCoeff1 (hρ₁ : ∀ (g : AbsGalQ2) (w : W₁), g • w = ρ g • w)
    (hρ₂ : ∀ (g : AbsGalQ2) (w : W₂), g • w = ρ g • w)
    (f : W₁ →+ W₂) (hf : Continuous f) (hcompat : ∀ (g : AbsGalQ2) (w : W₁), f (g • w) = g • f w)
    (x : H1 AbsGalQ2 W₁) (φ : W₂ →+ ZMod 2) :
    phiRes ρ (mapCoeff1 f hf hcompat x) φ = phiRes ρ x (φ.comp f) := by
  have hb : H1mk AbsGalQ2 W₁ (Quotient.out x) = x := Quotient.out_eq x
  have hmap : H1mk AbsGalQ2 W₂
      (Z1comap (ContinuousMonoidHom.id AbsGalQ2) f hf (fun g n => hcompat g n)
        (Quotient.out x)) = mapCoeff1 f hf hcompat x := by
    conv_rhs => rw [← hb]
    exact (mapCoeff1_H1mk f hf hcompat (Quotient.out x)).symm
  have h1 := phiRes_of_rep hρ₂ hmap φ
  have h2 := phiRes_of_rep hρ₁ hb (φ.comp f)
  rw [← h1, ← h2]
  rfl

end Naturality

/-! ## The main theorem: `FamiliesExtend` from the regular-summand package -/

variable {V : Type} [AddCommGroup V] [TopologicalSpace V] [DiscreteTopology V] [Finite V]
  [DistribMulAction AbsGalQ2 V] [ContinuousSMul AbsGalQ2 V] [DistribMulAction C V]

variable {ρ}

set_option maxHeartbeats 1000000 in
/-- **`FamiliesExtend` from the Lemma 6.11 package** (P-15f8): given the equivariant
split-summand package `(ι, r)` embedding `V` into the regular module `𝔽₂[C]^{Nr}`
(the `lemma_6_11`/`lemma_6_11_of_tame_pair` output shape), every admissible family extends to
a class of `H¹(ℚ₂, V)`.

Inverse Shapiro at the regular module (the explicit coinduced-coefficient cocycle out of the
family's evaluation seeds), then the retract transfer along `mapCoeff1 r`.  The statement is
`V`-side only; the regular module and its actions live inside the proof. -/
theorem familiesExtend_of_package
    (hρ : ∀ (g : AbsGalQ2) (v : V), g • v = ρ g • v)
    (hρsurj : Function.Surjective ⇑ρ) {Nr : ℕ}
    (ι : V →+ (Fin Nr → C → ZMod 2)) (r : (Fin Nr → C → ZMod 2) →+ V)
    (hι : ∀ (h : C) (v : V) (n : Fin Nr) (x : C), ι (h • v) n x = ι v n (h⁻¹ * x))
    (hr : ∀ (h : C) (F : Fin Nr → C → ZMod 2), r (fun n x => F n (h⁻¹ * x)) = h • r F)
    (hri : ∀ v : V, r (ι v) = v) :
    FamiliesExtend (V := V) ρ := by
  classical
  intro ξ
  -- move the package to the instance-opaque carrier
  let ι' : V →+ RegMod C Nr := ι
  let r' : RegMod C Nr →+ V := r
  -- the `G_ℚ₂`-action through `ρ` (the `C`-action is the global left-translation instance)
  letI instGR : DistribMulAction AbsGalQ2 (RegMod C Nr) :=
    DistribMulAction.compHom _ ρ.toMonoidHom
  haveI : ContinuousSMul AbsGalQ2 (RegMod C Nr) := by
    refine ⟨?_⟩
    have hfac : (fun p : AbsGalQ2 × RegMod C Nr => p.1 • p.2)
        = (fun q : C × RegMod C Nr => q.1 • q.2)
          ∘ (fun p : AbsGalQ2 × RegMod C Nr => (ρ p.1, p.2)) := by
      funext p
      rfl
    rw [hfac]
    exact continuous_of_discreteTopology.comp
      ((ρ.continuous_toFun.comp continuous_fst).prodMk continuous_snd)
  haveI : IsTopologicalAddGroup V :=
    { continuous_add := continuous_of_discreteTopology
      continuous_neg := continuous_of_discreteTopology }
  have hρR : ∀ (g : AbsGalQ2) (F : RegMod C Nr), g • F = ρ g • F := fun _ _ => rfl
  -- the family pushed to the regular module
  set Ξ : (RegMod C Nr →+ ZMod 2)
      → H1 ↥(ρ.toMonoidHom.ker : Subgroup AbsGalQ2) (ZMod 2) :=
    fun ψ => ξ.fam (ψ.comp ι') with hΞdef
  -- ι is `AbsGalQ2`-equivariant (through `ρ`, via the package's translation form)
  have hιG : ∀ (g : AbsGalQ2) (v : V), ι' (g • v) = g • ι' v := by
    intro g v
    show ι (g • v) = (fun n x => ι v n ((ρ g)⁻¹ * x) : RegMod C Nr)
    funext n x
    rw [hρ g v, hι (ρ g) v n x]
  -- Ξ is additive and conjugation-equivariant
  have hΞadd : ∀ ψ ψ', Ξ (ψ + ψ') = Ξ ψ + Ξ ψ' := by
    intro ψ ψ'
    show ξ.fam ((ψ + ψ').comp ι') = ξ.fam (ψ.comp ι') + ξ.fam (ψ'.comp ι')
    rw [AddMonoidHom.add_comp, ξ.add']
  have hΞequiv : ∀ (g : AbsGalQ2) (ψ : RegMod C Nr →+ ZMod 2),
      conjAct ρ g (Ξ ψ)
        = Ξ (ψ.comp (DistribSMul.toAddMonoidHom (RegMod C Nr) g⁻¹)) := by
    intro g ψ
    show conjAct ρ g (ξ.fam (ψ.comp ι'))
      = ξ.fam ((ψ.comp (DistribSMul.toAddMonoidHom (RegMod C Nr) g⁻¹)).comp ι')
    rw [ξ.equiv' g]
    congr 1
    ext v
    show ψ (ι' (g⁻¹ • v)) = ψ (g⁻¹ • ι' v)
    rw [hιG g⁻¹ v]
  -- the evaluation seeds and the Shapiro cocycle
  set u : Fin Nr → ↥(Z1 ↥(ρ.toMonoidHom.ker : Subgroup AbsGalQ2) (ZMod 2)) :=
    fun n => Quotient.out (Ξ (evReg Nr n 1)) with hudef
  have hu_mk : ∀ n, H1mk ↥(ρ.toMonoidHom.ker : Subgroup AbsGalQ2) (ZMod 2) (u n)
      = Ξ (evReg Nr n 1) := fun n => Quotient.out_eq _
  have hu_hom : ∀ (n : Fin Nr) (a b : ↥(ρ.toMonoidHom.ker : Subgroup AbsGalQ2)),
      (u n).1 (a * b) = (u n).1 a + (u n).1 b := by
    intro n a b
    obtain ⟨-, hcoc⟩ := mem_Z1_iff.mp (u n).2
    rw [hcoc a b]
    rfl
  set b : AbsGalQ2 → RegMod C Nr :=
    fun g => fun n x => (u n).1 (shapiroWord ρ hρsurj g x) with hbdef
  have hbZ1 : b ∈ Z1 AbsGalQ2 (RegMod C Nr) := by
    refine mem_Z1_iff.mpr ⟨?_, ?_⟩
    · show Continuous fun g : AbsGalQ2 => (fun n x => (u n).1 (shapiroWord ρ hρsurj g x)
        : Fin Nr → C → ZMod 2)
      refine continuous_pi fun n => continuous_pi fun x => ?_
      exact (mem_Z1_iff.mp (u n).2).1.comp (continuous_shapiroWord ρ hρsurj x)
    · intro g h
      funext n x
      show (u n).1 (shapiroWord ρ hρsurj (g * h) x)
        = (u n).1 (shapiroWord ρ hρsurj g x) + (u n).1 (shapiroWord ρ hρsurj h ((ρ g)⁻¹ * x))
      rw [shapiroWord_mul ρ hρsurj g h x, hu_hom]
  set xR : H1 AbsGalQ2 (RegMod C Nr) :=
    H1mk AbsGalQ2 (RegMod C Nr) ⟨b, hbZ1⟩ with hxRdef
  -- seed agreement at `ev (n, 1)`
  have hev1 : ∀ n : Fin Nr, phiRes ρ xR (evReg Nr n 1) = Ξ (evReg Nr n 1) := by
    intro n
    have hrep := phiRes_of_rep (ρ := ρ) hρR (b := ⟨b, hbZ1⟩) (x := xR) hxRdef.symm
      (evReg Nr n 1)
    rw [← hrep, ← hu_mk n]
    have hfun : (fun n₀ : ↥(ρ.toMonoidHom.ker : Subgroup AbsGalQ2) =>
        evReg Nr n 1 ((⟨b, hbZ1⟩ : ↥(Z1 AbsGalQ2 (RegMod C Nr))).1 (n₀ : AbsGalQ2)))
        = (u n).1 := by
      funext n₀
      show (u n).1 (shapiroWord ρ hρsurj (n₀ : AbsGalQ2) 1) = (u n).1 n₀
      rw [shapiroWord_ker_one ρ hρsurj n₀]
    rw [hfun, H1ofFun_of_mem (u n).2]
  -- the conjugation bootstrap: agreement at every `ev (n, c)`
  have hev : ∀ (n : Fin Nr) (c : C), phiRes ρ xR (evReg Nr n c) = Ξ (evReg Nr n c) := by
    intro n c
    have hgc : ρ (Function.surjInv hρsurj c) = c := Function.surjInv_eq hρsurj c
    set g : AbsGalQ2 := Function.surjInv hρsurj c
    have hcomp : (evReg Nr n 1).comp
        (DistribSMul.toAddMonoidHom (RegMod C Nr) g⁻¹) = evReg Nr n c := by
      ext F
      show (g⁻¹ • F) n 1 = F n c
      show F n ((ρ g⁻¹)⁻¹ * 1) = F n c
      rw [map_inv, inv_inv, mul_one, hgc]
    have h1 := phiRes_conj (ρ := ρ) hρR xR (evReg Nr n 1) g
    have h2 := hΞequiv g (evReg Nr n 1)
    rw [hcomp] at h1 h2
    rw [← h1, ← h2, hev1 n]
  -- span upgrade: agreement on every functional of the regular module
  have hall : ∀ ψ : RegMod C Nr →+ ZMod 2, phiRes ρ xR ψ = Ξ ψ := by
    -- finite-sum additivity for both sides, by induction on the finset
    have hsum : ∀ (T : (RegMod C Nr →+ ZMod 2)
          → H1 ↥(ρ.toMonoidHom.ker : Subgroup AbsGalQ2) (ZMod 2)),
        T 0 = 0 → (∀ ψ₁ ψ₂, T (ψ₁ + ψ₂) = T ψ₁ + T ψ₂) →
        ∀ s : Finset (Fin Nr × C),
          T (∑ p ∈ s, evReg Nr p.1 p.2) = ∑ p ∈ s, T (evReg Nr p.1 p.2) := by
      intro T h0 hadd s
      induction s using Finset.induction_on with
      | empty => rw [Finset.sum_empty, Finset.sum_empty, h0]
      | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, hadd, ih]
    have hz0 : Ξ 0 = 0 := by
      have h2 : Ξ 0 + Ξ 0 = Ξ 0 + 0 := by rw [← hΞadd 0 0, add_zero, add_zero]
      exact add_left_cancel h2
    have hp0 : phiRes ρ xR 0 = 0 := by
      have h1 : phiRes ρ xR 0 + phiRes ρ xR 0 = phiRes ρ xR 0 + 0 := by
        rw [← phiRes_add_phi (ρ := ρ) hρR xR 0 0, add_zero, add_zero]
      exact add_left_cancel h1
    intro ψ
    haveI : Fintype C := Fintype.ofFinite C
    rw [addHom_eq_sum_evReg Nr ψ,
      hsum (phiRes ρ xR) hp0 (phiRes_add_phi (ρ := ρ) hρR xR) _,
      hsum Ξ hz0 hΞadd _]
    exact Finset.sum_congr rfl fun p _ => hev p.1 p.2
  -- the retract transfer: pull the extending class back to `V`
  have hcompat_r : ∀ (g : AbsGalQ2) (F : RegMod C Nr), r' (g • F) = g • r' F := by
    intro g F
    have h1 : r' (g • F) = r (fun n x => F n ((ρ g)⁻¹ * x)) := rfl
    rw [h1, hr (ρ g) F, ← hρ g (r F)]
    rfl
  refine ⟨mapCoeff1 r' continuous_of_discreteTopology hcompat_r xR, fun φ => ?_⟩
  rw [phiRes_mapCoeff1 hρR hρ r' continuous_of_discreteTopology hcompat_r xR φ,
    hall (φ.comp r')]
  show ξ.fam ((φ.comp r').comp ι') = ξ.fam φ
  congr 1
  ext v
  show φ (r (ι v)) = φ v
  rw [hri v]

end ShapiroExtend

end GQ2
