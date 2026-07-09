import GQ2.EvensKahn
import GQ2.KummerKrullBridge

/-!
# B12 discharge — surjectivity of `kummerClassK` (hom/kernel layer B12-1 + capstone B12-3)

Groundwork for proving `GQ2.kummerClassK_surjective` (`Foundations/Axioms.lean`) in-repo,
retiring axiom **B12** (census 15 → 14).  See `docs/b12-tickets.md` / `docs/b12-proof-plan.md`.

This file is the **hom/kernel layer** (B12-1): it turns a degree-1 class
`c ∈ H¹(G_k, 𝔽₂)` — via `H1mk_surjective`, some cocycle `z ∈ Z¹` — into an open, index-2
subgroup of `G_k = k.fixingSubgroup` (its kernel, when `z ≠ 0`), plus the bookkeeping needed to
reconnect a Kummer cocycle to `z` at the end (`eq_of_zero_set`, `mem_zHom_ker`) and the `z = 0`
base case (`kummerClassK_one`).  It lives strictly upstream of `Foundations/Axioms.lean`
(imports only `GQ2.EvensKahn` + Mathlib) so the eventual flip is the zero-churn B11 pattern.

The Krull bridge that consumes `zHom_ker_isOpen` + `zHom_index_ker` to produce the quadratic
subextension is ticket B12-2 (`GQ2.KummerKrullBridge.exists_quadratic_of_open_index_two`,
imported above).  The **capstone** (B12-3) is assembled below as `kummerClassK_surjective'`, after
five `private` field-theory ports; `Foundations/Axioms.lean` calls it at the B12-4 census flip.
-/

namespace GQ2.KummerSurjectivity

open GQ2 ContCoh Kummer

local notation "ℚ̄₂" => AlgebraicClosure ℚ_[2]

variable (k : IntermediateField ℚ_[2] ℚ̄₂)

/-- The `k.fixingSubgroup`-action on `ZMod 2` is trivial (it factors through `Kummer`'s trivial
action on `𝔽₂`).  This is the `htriv` input of `mem_Z1_iff_of_trivial` for `G = G_k`. -/
lemma htriv_fs : ∀ (g : ↥k.fixingSubgroup) (m : ZMod 2), g • m = m := fun _ _ ↦ rfl

/-- A degree-1 cocycle `z ∈ Z¹(G_k, 𝔽₂)` as a genuine group homomorphism
`G_k →* Multiplicative (ZMod 2)` (trivial action ⇒ `z` is additive, `Z1_apply_one` ⇒ `z 1 = 0`).
Its kernel is the index-2 subgroup that the Krull bridge (B12-2) turns into a quadratic
subextension. -/
noncomputable def zHom (z : Z1 (↥k.fixingSubgroup) (ZMod 2)) :
    ↥k.fixingSubgroup →* Multiplicative (ZMod 2) where
  toFun g := Multiplicative.ofAdd (z.1 g)
  map_one' := by
    show Multiplicative.ofAdd (z.1 1) = 1
    rw [Z1_apply_one z]; rfl
  map_mul' a b := by
    show Multiplicative.ofAdd (z.1 (a * b))
      = Multiplicative.ofAdd (z.1 a) * Multiplicative.ofAdd (z.1 b)
    rw [((mem_Z1_iff_of_trivial (htriv_fs k)).mp z.2).2 a b, ofAdd_add]

variable {k}

@[simp] lemma zHom_apply (z : Z1 (↥k.fixingSubgroup) (ZMod 2)) (g : ↥k.fixingSubgroup) :
    zHom k z g = Multiplicative.ofAdd (z.1 g) := rfl

/-- The kernel of `zHom` is exactly the zero-set of the cocycle. -/
lemma mem_zHom_ker {z : Z1 (↥k.fixingSubgroup) (ZMod 2)} {g : ↥k.fixingSubgroup} :
    g ∈ (zHom k z).ker ↔ z.1 g = 0 := by
  rw [MonoidHom.mem_ker, zHom_apply, ofAdd_eq_one]

/-- The kernel of `zHom` is open: it is the preimage of the (open, discrete) point `{0}` under
the continuous cocycle `z`. -/
lemma zHom_ker_isOpen (z : Z1 (↥k.fixingSubgroup) (ZMod 2)) :
    IsOpen ((zHom k z).ker : Set ↥k.fixingSubgroup) := by
  have hset : ((zHom k z).ker : Set ↥k.fixingSubgroup) = z.1 ⁻¹' {0} := by
    ext g; rw [SetLike.mem_coe, mem_zHom_ker]; rfl
  rw [hset]
  exact ((mem_Z1_iff.mp z.2).1).isOpen_preimage _ (isOpen_discrete _)

/-- When the cocycle is nonzero, `zHom` is surjective (its 2-element codomain leaves no room
for a proper nontrivial image). -/
lemma zHom_surjective {z : Z1 (↥k.fixingSubgroup) (ZMod 2)} (hz : z.1 ≠ 0) :
    Function.Surjective (zHom k z) := by
  obtain ⟨g₀, hg₀⟩ := Function.ne_iff.mp hz
  have h1 : z.1 g₀ = 1 := (by decide : ∀ x : ZMod 2, x ≠ 0 → x = 1) _ hg₀
  intro y
  obtain ⟨x, rfl⟩ := Multiplicative.ofAdd.surjective y
  rcases (by decide : ∀ x : ZMod 2, x = 0 ∨ x = 1) x with rfl | rfl
  · exact ⟨1, by rw [zHom_apply, Z1_apply_one z]⟩
  · exact ⟨g₀, by rw [zHom_apply, h1]⟩

/-- When the cocycle is nonzero, the kernel has index 2. -/
lemma zHom_index_ker {z : Z1 (↥k.fixingSubgroup) (ZMod 2)} (hz : z.1 ≠ 0) :
    (zHom k z).ker.index = 2 := by
  rw [Subgroup.index_ker, MonoidHom.range_eq_top_of_surjective _ (zHom_surjective hz),
    Nat.card_congr Subgroup.topEquiv.toEquiv, Nat.card_eq_fintype_card]
  decide

/-- Two `𝔽₂`-valued functions with the same zero-set are equal (the only nonzero value is `1`).
This reconnects a Kummer cocycle to `z` in the capstone (B12-3): equal kernels ⇒ equal cocycles
⇒ equal `H¹`-classes. -/
lemma eq_of_zero_set {f f' : ↥k.fixingSubgroup → ZMod 2}
    (h : ∀ g, f g = 0 ↔ f' g = 0) : f = f' := by
  funext g
  by_cases hf : f g = 0
  · rw [hf, (h g).mp hf]
  · rw [(by decide : ∀ x : ZMod 2, x ≠ 0 → x = 1) (f g) hf,
      (by decide : ∀ x : ZMod 2, x ≠ 0 → x = 1) (f' g) (fun c => hf ((h g).mpr c))]

/-- **The `z = 0` base case.**  `[1] = 0`: the Kummer class of the unit `1` vanishes.  Ported
(direct proof) from `HilbertLedger.kummerClassK_one`, which is downstream of the axiom file.
`sqrtCl 1` is a square root of `1` in `ℚ̄₂`, hence `±1 ∈ ℚ₂`, hence Galois-fixed, so the cocycle
is identically `0`. -/
theorem kummerClassK_one : kummerClassK k (1 : (↥k)ˣ) = 0 := by
  have hfix : ∀ g : GaloisGroup ℚ_[2], g • sqrtCl ((((1 : (↥k)ˣ) : ↥k) : ℚ̄₂)) = sqrtCl 1 := by
    intro g
    have hsq : sqrtCl ((((1 : (↥k)ˣ) : ↥k) : ℚ̄₂)) = sqrtCl (1 : ℚ̄₂) := by norm_num
    rw [hsq]
    have h2 : (sqrtCl (1 : ℚ̄₂) - 1) * (sqrtCl (1 : ℚ̄₂) + 1) = 0 := by
      have := sqrtCl_sq (1 : ℚ̄₂); linear_combination this
    rcases mul_eq_zero.1 h2 with h' | h'
    · have : sqrtCl (1 : ℚ̄₂) = 1 := by linear_combination h'
      rw [this, AlgEquiv.smul_def, map_one]
    · have : sqrtCl (1 : ℚ̄₂) = -1 := by linear_combination h'
      rw [this, AlgEquiv.smul_def, map_neg, map_one]
  have hzero : (kummerClassK k (1 : (↥k)ˣ)) = H1mk _ _ 0 := by
    rw [kummerClassK]
    congr 1
    apply Subtype.ext
    funext g
    show kummerCocycleFun (sqrtCl ((((1 : (↥k)ˣ) : ↥k) : ℚ̄₂))) _ = 0
    exact kummerCocycleFun_eq0 (hfix _)
  rw [hzero, map_zero]

/-! ## B12-3: private field-theory ports + the capstone

Ports (verbatim-modulo-namespace) of the field-theory lemmas the capstone needs, from files that
sit *downstream* of `Foundations/Axioms.lean`: `fixingSubgroup_adjoin_simple`, `mem_bot_iff_mem`,
`exists_sqrt_generator`, `fixingSubgroup_subgroupOf_eq_stabilizer` (`GQ2/QuadraticAdjoin.lean`) and
`kcf_root_indep'` (`GQ2/HilbertLedger.lean`).  Kept `private` so they cannot clash with the
downstream originals or with B12-2's `private` degree lemmas.  The B12-2 Krull bridge
`exists_quadratic_of_open_index_two` is imported from `GQ2.KummerKrullBridge` (same namespace). -/

open IntermediateField

/-- Port of `QuadraticAdjoin.fixingSubgroup_adjoin_simple`: the fixing subgroup of a simple adjoin
`F⟮δ⟯` is exactly the stabilizer of the generator. -/
private theorem fixingSubgroup_adjoin_simple {F E : Type*} [Field F] [Field E] [Algebra F E]
    (δ : E) :
    (IntermediateField.adjoin F {δ}).fixingSubgroup
      = MulAction.stabilizer (E ≃ₐ[F] E) δ := by
  ext σ
  rw [IntermediateField.mem_fixingSubgroup_iff, MulAction.mem_stabilizer_iff, AlgEquiv.smul_def]
  constructor
  · intro h
    exact h δ (IntermediateField.mem_adjoin_simple_self F δ)
  · intro hσ x hx
    have hst : Subgroup.zpowers σ ≤ MulAction.stabilizer (E ≃ₐ[F] E) δ :=
      Subgroup.zpowers_le.mpr
        (MulAction.mem_stabilizer_iff.mpr ((AlgEquiv.smul_def σ δ).trans hσ))
    have hle : IntermediateField.adjoin F {δ}
        ≤ IntermediateField.fixedField (Subgroup.zpowers σ) := by
      rw [IntermediateField.adjoin_simple_le_iff, IntermediateField.mem_fixedField_iff]
      intro f hf
      exact (AlgEquiv.smul_def f δ).symm.trans (MulAction.mem_stabilizer_iff.mp (hst hf))
    exact (IntermediateField.mem_fixedField_iff _ _).mp (hle hx) σ (Subgroup.mem_zpowers σ)

/-- Port of `QuadraticAdjoin.mem_bot_iff_mem`: membership in `⊥ : IntermediateField ↥k ℚ̄₂` is
membership in `k`. -/
private theorem mem_bot_iff_mem (k : IntermediateField ℚ_[2] ℚ̄₂) (x : ℚ̄₂) :
    x ∈ (⊥ : IntermediateField ↥k ℚ̄₂) ↔ x ∈ k := by
  rw [IntermediateField.mem_bot]
  constructor
  · rintro ⟨y, rfl⟩
    exact y.2
  · intro hx
    exact ⟨⟨x, hx⟩, rfl⟩

/-- Port of `QuadraticAdjoin.exists_sqrt_generator` (**complete the square**): a degree-2 extension
of intermediate fields of `ℚ̄₂/ℚ_[2]` has a square-root generator `δ ∈ L ∖ k` with `δ² = d ∈ kˣ`,
`L = k⟮δ⟯`. -/
private theorem exists_sqrt_generator {k L : IntermediateField ℚ_[2] ℚ̄₂} (hkL : k ≤ L)
    (hdeg : Module.finrank ↥k ↥(extendScalars hkL) = 2) :
    ∃ (d : (↥k)ˣ) (δ : ℚ̄₂), δ ^ 2 = ((d : ↥k) : ℚ̄₂) ∧ δ ∈ L ∧ δ ∉ k ∧
      IntermediateField.adjoin ↥k {δ} = extendScalars hkL := by
  haveI hfinL : FiniteDimensional ↥k ↥(extendScalars hkL) :=
    Module.finite_of_finrank_pos (by rw [hdeg]; norm_num)
  have hne : extendScalars hkL ≠ ⊥ := by
    intro h
    rw [h, IntermediateField.finrank_bot] at hdeg
    exact absurd hdeg (by norm_num)
  obtain ⟨θ, hθmem, hθbot⟩ := SetLike.exists_of_lt hne.bot_lt
  have hθk : θ ∉ k := fun h => hθbot ((mem_bot_iff_mem k θ).mpr h)
  have hθL : θ ∈ L := hθmem
  have hθint : IsIntegral ↥k θ := (Algebra.IsAlgebraic.isAlgebraic θ).isIntegral
  haveI hfinθ : FiniteDimensional ↥k ↥(IntermediateField.adjoin ↥k {θ}) :=
    IntermediateField.adjoin.finiteDimensional hθint
  have hle : IntermediateField.adjoin ↥k {θ} ≤ extendScalars hkL := by
    rw [IntermediateField.adjoin_simple_le_iff]
    exact hθmem
  have h2le : 2 ≤ Module.finrank ↥k ↥(IntermediateField.adjoin ↥k {θ}) := by
    have hpos : 0 < Module.finrank ↥k ↥(IntermediateField.adjoin ↥k {θ}) := Module.finrank_pos
    have hne1 : Module.finrank ↥k ↥(IntermediateField.adjoin ↥k {θ}) ≠ 1 := fun h1 =>
      hθbot (IntermediateField.finrank_adjoin_simple_eq_one_iff.mp h1)
    omega
  have heq : IntermediateField.adjoin ↥k {θ} = extendScalars hkL :=
    IntermediateField.eq_of_le_of_finrank_le hle (by rw [hdeg]; exact h2le)
  have hpdeg : (minpoly ↥k θ).natDegree = 2 := by
    have hfr := IntermediateField.adjoin.finrank hθint
    rw [heq, hdeg] at hfr
    exact hfr.symm
  set a : ↥k := (minpoly ↥k θ).coeff 1 with ha
  set b : ↥k := (minpoly ↥k θ).coeff 0 with hb
  have hrel : θ ^ 2 + (a : ℚ̄₂) * θ + (b : ℚ̄₂) = 0 := by
    have haev := minpoly.aeval ↥k θ
    rw [Polynomial.aeval_eq_sum_range' (n := 3) (by rw [hpdeg]; norm_num) θ,
      Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_one] at haev
    have hc2 : (minpoly ↥k θ).coeff 2 = 1 := by
      have hmc := (minpoly.monic hθint).coeff_natDegree
      rwa [hpdeg] at hmc
    rw [hc2, pow_zero, pow_one, one_smul, Algebra.smul_def, Algebra.smul_def, mul_one] at haev
    calc θ ^ 2 + (a : ℚ̄₂) * θ + (b : ℚ̄₂)
        = (b : ℚ̄₂) + (a : ℚ̄₂) * θ + θ ^ 2 := by ring
      _ = 0 := haev
  set δ : ℚ̄₂ := 2 * θ + (a : ℚ̄₂) with hδdef
  set dd : ↥k := a ^ 2 - (b + b + b + b) with hdd
  have hδ2 : δ ^ 2 = ((dd : ↥k) : ℚ̄₂) := by
    have hcast : ((dd : ↥k) : ℚ̄₂)
        = (a : ℚ̄₂) ^ 2 - ((b : ℚ̄₂) + (b : ℚ̄₂) + (b : ℚ̄₂) + (b : ℚ̄₂)) := by
      rw [hdd]; push_cast; ring
    rw [hδdef, hcast]
    linear_combination (4 : ℚ̄₂) * hrel
  have h2k : (2 : ℚ̄₂) ∈ k := by simp
  have hθrec : θ = (δ - (a : ℚ̄₂)) * (2 : ℚ̄₂)⁻¹ := by
    rw [hδdef]
    field_simp
    ring
  have hδk : δ ∉ k := by
    intro hδmem
    refine hθk ?_
    rw [hθrec]
    exact k.mul_mem (k.sub_mem hδmem a.2) (k.inv_mem h2k)
  have hδL : δ ∈ L := by
    rw [hδdef]
    refine L.add_mem ?_ (hkL a.2)
    rw [two_mul]
    exact L.add_mem hθL hθL
  have hdd0 : dd ≠ 0 := by
    intro h0
    refine hδk ?_
    have hz : δ ^ 2 = 0 := by rw [hδ2, h0]; simp
    have hδ0 : δ = 0 := (pow_eq_zero_iff two_ne_zero).mp hz
    rw [hδ0]
    exact k.zero_mem
  have hadj : IntermediateField.adjoin ↥k {δ} = IntermediateField.adjoin ↥k {θ} := by
    apply le_antisymm
    · rw [IntermediateField.adjoin_simple_le_iff, hδdef]
      refine add_mem ?_ ((IntermediateField.adjoin ↥k {θ}).algebraMap_mem a)
      rw [two_mul]
      exact add_mem (IntermediateField.mem_adjoin_simple_self ↥k θ)
        (IntermediateField.mem_adjoin_simple_self ↥k θ)
    · rw [IntermediateField.adjoin_simple_le_iff, hθrec]
      refine mul_mem (sub_mem (IntermediateField.mem_adjoin_simple_self ↥k δ)
        ((IntermediateField.adjoin ↥k {δ}).algebraMap_mem a)) (inv_mem ?_)
      simp
  exact ⟨Units.mk0 dd hdd0, δ, hδ2, hδL, hδk, hadj.trans heq⟩

/-- Port of `QuadraticAdjoin.fixingSubgroup_subgroupOf_eq_stabilizer`: inside `G_k`, fixing `L`
pointwise is stabilizing `δ` (for `L = k⟮δ⟯`). -/
private theorem fixingSubgroup_subgroupOf_eq_stabilizer {k L : IntermediateField ℚ_[2] ℚ̄₂}
    (hkL : k ≤ L) {δ : ℚ̄₂}
    (hadj : IntermediateField.adjoin ↥k {δ} = extendScalars hkL) :
    (L.fixingSubgroup).subgroupOf (k.fixingSubgroup)
      = (MulAction.stabilizer (Kummer.GaloisGroup ℚ_[2]) δ).subgroupOf (k.fixingSubgroup) := by
  have key := fixingSubgroup_adjoin_simple (F := ↥k) (E := ℚ̄₂) δ
  rw [hadj] at key
  ext g
  have hmem := SetLike.ext_iff.mp key (IntermediateField.fixingSubgroupEquiv k g)
  simp only [IntermediateField.mem_fixingSubgroup_iff, MulAction.mem_stabilizer_iff,
    AlgEquiv.smul_def] at hmem
  rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf,
    IntermediateField.mem_fixingSubgroup_iff, MulAction.mem_stabilizer_iff, AlgEquiv.smul_def]
  exact hmem

/-- Port of `HilbertLedger.kcf_root_indep'`: two square roots of the same `ℚ̄₂`-element give the
same Kummer cocycle (`α² = β²` forces `α = ±β`, and `κ` is sign-insensitive). -/
private lemma kcf_root_indep' {α β : ℚ̄₂} (h : α ^ 2 = β ^ 2) :
    kummerCocycleFun α = kummerCocycleFun β := by
  have h2 : (α - β) * (α + β) = 0 := by linear_combination h
  rcases mul_eq_zero.1 h2 with h' | h'
  · rw [sub_eq_zero.1 h']
  · rw [add_eq_zero_iff_eq_neg.1 h', kummerCocycleFun_neg]

/-- Zero-characterization of the Kummer cocycle: `κ_x(γ) = 0 ↔ γ` fixes `x`. -/
private lemma kcf_eq_zero_iff (x : ℚ̄₂) (γ : Kummer.GaloisGroup ℚ_[2]) :
    kummerCocycleFun x γ = 0 ↔ γ • x = x := by
  constructor
  · intro h
    by_contra hne
    rw [kummerCocycleFun, if_neg hne] at h
    exact (by decide : (1 : ZMod 2) ≠ 0) h
  · exact kummerCocycleFun_eq0

/-- **The capstone** (B12-3): every degree-1 class `c ∈ H¹(G_k, 𝔽₂)` is a Kummer class
`kummerClassK k a`.  If the representing cocycle `z` is `0`, `c = kummerClassK k 1`; otherwise its
kernel is an open index-2 subgroup, which the B12-2 bridge turns into a quadratic `L = k⟮δ⟯`, and
completing the square exhibits `d ∈ kˣ` whose Kummer cocycle vanishes on exactly `ker z = Stab δ` —
so, both being `𝔽₂`-homs, `kummerClassK k d = c`.  Consumed by `Foundations/Axioms.lean` at the
B12-4 census flip (same-name theorem, zero consumer churn). -/
theorem kummerClassK_surjective' (k : IntermediateField ℚ_[2] ℚ̄₂) [FiniteDimensional ℚ_[2] k] :
    Function.Surjective (kummerClassK k) := by
  intro c
  obtain ⟨z, rfl⟩ := H1mk_surjective c
  by_cases hz0 : z.1 = 0
  · have hzzero : z = 0 := Subtype.ext hz0
    exact ⟨1, by rw [kummerClassK_one, hzzero, map_zero]⟩
  · obtain ⟨L, hkL, _hFinL, hsubEq, hdeg2⟩ :=
      exists_quadratic_of_open_index_two k (zHom k z).ker (zHom_ker_isOpen z) (zHom_index_ker hz0)
    obtain ⟨d, δ, hδ2, _hδL, _hδk, hadj⟩ := exists_sqrt_generator hkL hdeg2
    have hker : (zHom k z).ker
        = (MulAction.stabilizer (Kummer.GaloisGroup ℚ_[2]) δ).subgroupOf k.fixingSubgroup :=
      hsubEq.symm.trans (fixingSubgroup_subgroupOf_eq_stabilizer hkL hadj)
    have hcf : kummerCocycleFun (sqrtCl ((↑d : ↥k) : ℚ̄₂)) = kummerCocycleFun δ :=
      kcf_root_indep' (by rw [sqrtCl_sq]; exact hδ2.symm)
    refine ⟨d, ?_⟩
    rw [kummerClassK]
    congr 1
    apply Subtype.ext
    refine eq_of_zero_set (fun g => ?_)
    have hL : kummerCocycleFun (sqrtCl ((↑d : ↥k) : ℚ̄₂))
          ((g : k.fixingSubgroup) : Kummer.GaloisGroup ℚ_[2]) = 0
        ↔ ((g : k.fixingSubgroup) : Kummer.GaloisGroup ℚ_[2]) • δ = δ := by
      rw [hcf]; exact kcf_eq_zero_iff _ _
    have hR : z.1 g = 0
        ↔ ((g : k.fixingSubgroup) : Kummer.GaloisGroup ℚ_[2]) • δ = δ := by
      rw [← mem_zHom_ker, hker, Subgroup.mem_subgroupOf, MulAction.mem_stabilizer_iff]
    exact hL.trans hR.symm

end GQ2.KummerSurjectivity
