/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Opus-4.8 and Fable-5
-/
module

public import GQ2.Dyadic.LocalGauss.Q0
public import GQ2.LocalLiftingDuality

@[expose] public section

/-!
# The Tate pairing at the splitting group, over a general local source (LG2)

Clone-retype of `GQ2/DeepDualityK.lean` (the ℚ₂ "K-level Tate pairing") with the ambient
`G_ℚ₂` replaced by an arbitrary topological group `Γ`.  In the dyadic campaign `Γ = G_K = ↥U`
for `U ≤ G_ℚ₂` open of finite index, and the inner splitting group is `N_K = ker ρ ≤ Γ`; the
`AbsGalQ2`-anchoring of `N_K` (needed to talk about deep units) is available through
`GQ2.Dyadic.H1congrGroup` (`GQ2/Dyadic/LocalGauss/Q0.lean` §7), which transports `Hⁱ(↥N_K, −)`
to `Hⁱ(↥(N_K.map U.subtype), −)`.  The ℚ₂ originals are untouched (`docs/dyadic/lg-design.md`
§2: 13/13 clone, zero in-place edits).

## Contents

* §1 **conjugation transport** at a general `Γ`: `conjMap`, `conjAct`, its algebra
  (`conjAct_{add,zero,comp,one,inner,ker}`) and the `C`-module structure `conjModule` — the
  `Γ`-generic form of `GQ2.LocalKummer.{conjMap, conjAct, conjModule}`
  (`GQ2/LocalKummer.lean` :630–:820).  *Cloned here because `pairingK_conjAct` (an LG2 headline
  declaration) needs it; LG4's `LocalKummer` clone should consume these rather than re-clone.*
* §2 the coefficient bridge `zmodMuDualEquiv : 𝔽₂ ≃+ Hom(𝔽₂, μ₂)`.
* §3 `pairingK D := inv_N ∘ cup` on `H¹(N, 𝔽₂)` and **(H2)** `pairingK_nondeg` (the bundle's
  `perfect11` clause = B6).
* §4 **(H1)** `pairingK_conjAct` / `pairingK_conjModule`: conjugation invariance.
* §5 **the bundle producer** `ker_isLocalDualizingGroup`: if `Γ` is a local dualizing group and
  `C` is finite discrete, then so is `ker ρ` — generalizing `GQ2.ker_isLocalDualizingGroup`
  (`GQ2/DeepDualityK.lean` :70) from `Γ = G_ℚ₂` to any local dualizing `Γ`, so that the nested
  tower `N_K ≤ G_K = ↥U ≤ G_ℚ₂` is covered.  `tateDualityKer` feeds it to the base-generalized
  B6 axiom `GQ2.tateDualityAt`.

Axiom hygiene: `pairingK` and everything above it is **parametrized over the bundle** `D`, so it
prints the standard three — a subset of the ℚ₂ model's set (which bakes in `tateDualityAt`
through `GQ2.tateDualityK`).  Only `tateDualityKer` (§5) consumes B6, exactly as its model does.

The (H3) isotropy splice of the ℚ₂ file (`pairingK_deep_deep`, `pairingK_mid_deep`,
`midClassesSubgroup_le_pairPerp_pairingK`, `deepClassesSubgroup_le_pairPerp_pairingK`,
`GQ2/DeepDualityK.lean` :317–:578) is Kummer-theoretic: it lives over
`IntermediateField ℚ_[2] ℚ̄₂` and `IsDeepUnit`/`IsMidUnit`, whose home is the deep-unit package.
It is therefore left to LG4, which owns `DeepPackage.lean`; §1–§5 here are the group-side
prerequisites it consumes, together with `H1congrGroup` for the `↥N_K`-vs-`↥N` anchoring.
-/

namespace GQ2.Dyadic

open GQ2 GQ2.ContCoh

section Conjugation

variable {Γ : Type} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
  [DistribMulAction Γ (ZMod 2)] [ContinuousSMul Γ (ZMod 2)]
variable {C : Type} [Group C] [TopologicalSpace C]
variable (ρ : ContinuousMonoidHom Γ C)

/-! ## §1 Conjugation transport on `H¹(N, 𝔽₂)`, `N = ker ρ` -/

omit [IsTopologicalGroup Γ] [DistribMulAction Γ (ZMod 2)] [ContinuousSMul Γ (ZMod 2)] in
/-- Conjugation carries `N = ker ρ` into itself. -/
theorem conj_mem_ker (g : Γ) (n : ↥(ρ.toMonoidHom.ker : Subgroup Γ)) :
    g⁻¹ * (n : Γ) * g ∈ (ρ.toMonoidHom.ker : Subgroup Γ) := by
  simpa using (MonoidHom.normal_ker ρ.toMonoidHom).conj_mem (n : Γ) n.2 g⁻¹

/-- The conjugation self-map of `N = ker ρ`, `n ↦ g⁻¹ n g`. -/
def conjMap (g : Γ) (n : ↥(ρ.toMonoidHom.ker : Subgroup Γ)) :
    ↥(ρ.toMonoidHom.ker : Subgroup Γ) :=
  ⟨g⁻¹ * (n : Γ) * g, conj_mem_ker ρ g n⟩

omit [DistribMulAction Γ (ZMod 2)] [ContinuousSMul Γ (ZMod 2)] in
theorem continuous_conjMap (g : Γ) : Continuous (conjMap ρ g) :=
  Continuous.subtype_mk (((continuous_const.mul continuous_subtype_val).mul continuous_const)) _

omit [ContinuousSMul Γ (ZMod 2)] in
/-- Conjugation-precomposition preserves `Z¹(N, 𝔽₂)` (the coefficient action is trivial, so
cocycles are continuous homs and conjugation is a continuous endomorphism). -/
theorem comp_conjMap_mem_Z1 {f : ↥(ρ.toMonoidHom.ker : Subgroup Γ) → ZMod 2}
    (hf : f ∈ Z1 ↥(ρ.toMonoidHom.ker : Subgroup Γ) (ZMod 2)) (g : Γ) :
    (fun n => f (conjMap ρ g n)) ∈ Z1 ↥(ρ.toMonoidHom.ker : Subgroup Γ) (ZMod 2) := by
  obtain ⟨hfc, hcoc⟩ := mem_Z1_iff.mp hf
  refine mem_Z1_iff.mpr ⟨hfc.comp (continuous_conjMap ρ g), fun n m => ?_⟩
  show f (conjMap ρ g (n * m)) = f (conjMap ρ g n) + n • f (conjMap ρ g m)
  have hmul : conjMap ρ g (n * m) = conjMap ρ g n * conjMap ρ g m := by
    apply Subtype.ext
    show g⁻¹ * ((n : Γ) * m) * g = (g⁻¹ * n * g) * (g⁻¹ * m * g)
    group
  rw [hmul, hcoc, smul_zmodTwo, smul_zmodTwo]

omit [IsTopologicalGroup Γ] [DistribMulAction Γ (ZMod 2)] [ContinuousSMul Γ (ZMod 2)] in
/-- Conjugation composes contravariantly: `conjMap (g·h) = conjMap h ∘ conjMap g`. -/
theorem conjMap_mul (g h : Γ) (n : ↥(ρ.toMonoidHom.ker : Subgroup Γ)) :
    conjMap ρ (g * h) n = conjMap ρ h (conjMap ρ g n) := by
  apply Subtype.ext
  show (g * h)⁻¹ * (n : Γ) * (g * h) = h⁻¹ * (g⁻¹ * n * g) * h
  group

omit [IsTopologicalGroup Γ] [DistribMulAction Γ (ZMod 2)] [ContinuousSMul Γ (ZMod 2)] in
/-- `conjMap` is multiplicative in the kernel argument. -/
theorem conjMap_mul_apply (g : Γ) (n m : ↥(ρ.toMonoidHom.ker : Subgroup Γ)) :
    conjMap ρ g (n * m) = conjMap ρ g n * conjMap ρ g m := by
  apply Subtype.ext
  show g⁻¹ * ((n : Γ) * (m : Γ)) * g = (g⁻¹ * (n : Γ) * g) * (g⁻¹ * (m : Γ) * g)
  group

omit [IsTopologicalGroup Γ] [DistribMulAction Γ (ZMod 2)] [ContinuousSMul Γ (ZMod 2)] in
/-- `conjMap ρ g` inverts `conjMap ρ g⁻¹`. -/
theorem conjMap_conjMap_inv (g : Γ) (n : ↥(ρ.toMonoidHom.ker : Subgroup Γ)) :
    conjMap ρ g (conjMap ρ g⁻¹ n) = n := by
  apply Subtype.ext
  show g⁻¹ * ((g⁻¹)⁻¹ * (n : Γ) * g⁻¹) * g = (n : Γ)
  group

/-- **The conjugation action** of `g : Γ` on `H¹(N, 𝔽₂)`, `[f] ↦ [n ↦ f(g⁻¹ n g)]`. -/
noncomputable def conjAct (g : Γ) (ξ : H1 ↥(ρ.toMonoidHom.ker : Subgroup Γ) (ZMod 2)) :
    H1 ↥(ρ.toMonoidHom.ker : Subgroup Γ) (ZMod 2) :=
  H1ofFun ↥(ρ.toMonoidHom.ker : Subgroup Γ) (fun n => (Quotient.out ξ).1 (conjMap ρ g n))

/-- Computation rule for `conjAct` on the class of an explicit cocycle. -/
theorem conjAct_h1ofFun (g : Γ) {f : ↥(ρ.toMonoidHom.ker : Subgroup Γ) → ZMod 2}
    (hf : f ∈ Z1 ↥(ρ.toMonoidHom.ker : Subgroup Γ) (ZMod 2)) :
    conjAct ρ g (H1ofFun ↥(ρ.toMonoidHom.ker : Subgroup Γ) f)
      = H1ofFun ↥(ρ.toMonoidHom.ker : Subgroup Γ) (fun n => f (conjMap ρ g n)) := by
  set ξ := H1ofFun ↥(ρ.toMonoidHom.ker : Subgroup Γ) f with hξ
  have hout : (Quotient.out ξ : ↥(Z1 ↥(ρ.toMonoidHom.ker : Subgroup Γ) (ZMod 2))).1 = f := by
    have h1 : H1mk ↥(ρ.toMonoidHom.ker : Subgroup Γ) (ZMod 2) (Quotient.out ξ)
        = H1mk ↥(ρ.toMonoidHom.ker : Subgroup Γ) (ZMod 2) ⟨f, hf⟩ := by
      have hoe : H1mk ↥(ρ.toMonoidHom.ker : Subgroup Γ) (ZMod 2) (Quotient.out ξ) = ξ :=
        Quotient.out_eq ξ
      rw [hoe, hξ, H1ofFun_of_mem hf]
    have hz0 : H1mk ↥(ρ.toMonoidHom.ker : Subgroup Γ) (ZMod 2)
        (Quotient.out ξ - ⟨f, hf⟩) = 0 := by
      rw [map_sub, h1, sub_self]
    have hdiff := (QuotientAddGroup.eq_zero_iff _).mp hz0
    rw [AddSubgroup.mem_addSubgroupOf] at hdiff
    obtain ⟨w₀, hw₀⟩ := hdiff
    funext n
    have hn := congrFun hw₀ n
    have hz : (Quotient.out ξ - ⟨f, hf⟩ :
        ↥(Z1 ↥(ρ.toMonoidHom.ker : Subgroup Γ) (ZMod 2))).1 n = 0 := by
      rw [← hn]
      show n • w₀ - w₀ = 0
      rw [smul_zmodTwo, sub_self]
    have hsub : (Quotient.out ξ).1 n - f n = 0 := hz
    exact sub_eq_zero.mp hsub
  unfold conjAct
  rw [hout]

/-- **`conjAct` is additive**. -/
theorem conjAct_add (g : Γ) (ξ η : H1 ↥(ρ.toMonoidHom.ker : Subgroup Γ) (ZMod 2)) :
    conjAct ρ g (ξ + η) = conjAct ρ g ξ + conjAct ρ g η := by
  induction ξ using QuotientAddGroup.induction_on with
  | H a =>
    induction η using QuotientAddGroup.induction_on with
    | H b =>
      show conjAct ρ g (H1mk _ _ a + H1mk _ _ b)
        = conjAct ρ g (H1mk _ _ a) + conjAct ρ g (H1mk _ _ b)
      rw [← map_add, ← H1ofFun_of_mem (a + b).2, ← H1ofFun_of_mem a.2, ← H1ofFun_of_mem b.2,
        conjAct_h1ofFun ρ g (a + b).2, conjAct_h1ofFun ρ g a.2, conjAct_h1ofFun ρ g b.2]
      exact DeepPart.H1ofFun_add (comp_conjMap_mem_Z1 ρ a.2 g) (comp_conjMap_mem_Z1 ρ b.2 g)

/-- **`conjAct` preserves `0`** (from additivity). -/
theorem conjAct_zero (g : Γ) :
    conjAct ρ g (0 : H1 ↥(ρ.toMonoidHom.ker : Subgroup Γ) (ZMod 2)) = 0 := by
  have h : conjAct ρ g 0 + conjAct ρ g 0 = conjAct ρ g 0 := by
    rw [← conjAct_add ρ g 0 0, add_zero]
  exact add_eq_left.mp h

/-- **`conjAct` is a left action** (contravariant `conjMap` composition). -/
theorem conjAct_comp (g h : Γ) (ξ : H1 ↥(ρ.toMonoidHom.ker : Subgroup Γ) (ZMod 2)) :
    conjAct ρ (g * h) ξ = conjAct ρ g (conjAct ρ h ξ) := by
  induction ξ using QuotientAddGroup.induction_on with
  | H b =>
    rw [show (QuotientAddGroup.mk b : H1 ↥(ρ.toMonoidHom.ker : Subgroup Γ) (ZMod 2))
      = H1ofFun _ b.1 from (H1ofFun_of_mem b.2).symm,
      conjAct_h1ofFun ρ h b.2, conjAct_h1ofFun ρ (g * h) b.2,
      conjAct_h1ofFun ρ g (comp_conjMap_mem_Z1 ρ b.2 h)]
    exact congrArg _ (funext fun n => congrArg b.1 (conjMap_mul ρ g h n))

/-- **`conjAct` by the identity is the identity**. -/
theorem conjAct_one (ξ : H1 ↥(ρ.toMonoidHom.ker : Subgroup Γ) (ZMod 2)) :
    conjAct ρ 1 ξ = ξ := by
  induction ξ using QuotientAddGroup.induction_on with
  | H b =>
    rw [show (QuotientAddGroup.mk b : H1 ↥(ρ.toMonoidHom.ker : Subgroup Γ) (ZMod 2))
      = H1ofFun _ b.1 from (H1ofFun_of_mem b.2).symm, conjAct_h1ofFun ρ 1 b.2]
    refine congrArg _ (funext fun n => congrArg b.1 ?_)
    apply Subtype.ext
    show (1 : Γ)⁻¹ * (n : Γ) * 1 = n
    group

/-- **Inner conjugation is trivial on `H¹(N)`**: for `m ∈ N`, `conjAct ρ m = id`. -/
theorem conjAct_inner (m : ↥(ρ.toMonoidHom.ker : Subgroup Γ))
    (ξ : H1 ↥(ρ.toMonoidHom.ker : Subgroup Γ) (ZMod 2)) :
    conjAct ρ (m : Γ) ξ = ξ := by
  induction ξ using QuotientAddGroup.induction_on with
  | H b =>
    rw [show (QuotientAddGroup.mk b : H1 ↥(ρ.toMonoidHom.ker : Subgroup Γ) (ZMod 2))
      = H1ofFun _ b.1 from (H1ofFun_of_mem b.2).symm, conjAct_h1ofFun ρ (m : Γ) b.2]
    refine congrArg _ (funext fun n => ?_)
    obtain ⟨hc, hcoc⟩ := mem_Z1_iff.mp b.2
    have hb1 : b.1 1 = 0 := by
      have h := hcoc 1 1
      rw [mul_one, smul_zmodTwo] at h
      exact add_eq_left.mp h.symm
    -- `b(m⁻¹ n m) = b(m⁻¹) + b(n) + b(m)`, and `b(m⁻¹) + b(m) = b(1) = 0`
    have he : conjMap ρ (m : Γ) n = m⁻¹ * n * m := by
      apply Subtype.ext
      simp only [conjMap, Subgroup.coe_mul, Subgroup.coe_inv]
    have hmm : b.1 m⁻¹ + b.1 m = 0 := by
      have h := hcoc m⁻¹ m
      rw [inv_mul_cancel, smul_zmodTwo, hb1] at h
      exact h.symm
    rw [he, hcoc, hcoc, smul_zmodTwo, smul_zmodTwo,
      show b.1 m⁻¹ + b.1 n + b.1 m = (b.1 m⁻¹ + b.1 m) + b.1 n by ring, hmm, zero_add]

/-- **`conjAct` depends only on `ρ g`**. -/
theorem conjAct_ker (g g' : Γ) (hgg : ρ g = ρ g')
    (ξ : H1 ↥(ρ.toMonoidHom.ker : Subgroup Γ) (ZMod 2)) :
    conjAct ρ g ξ = conjAct ρ g' ξ := by
  have hgg' : ρ.toMonoidHom g = ρ.toMonoidHom g' := hgg
  have hm : g⁻¹ * g' ∈ (ρ.toMonoidHom.ker : Subgroup Γ) := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hgg', inv_mul_cancel]
  have hsplit : g' = g * (g⁻¹ * g') := by group
  rw [hsplit, conjAct_comp ρ g (g⁻¹ * g') ξ, conjAct_inner ρ ⟨g⁻¹ * g', hm⟩ ξ]

/-- **The `C`-module structure on `H¹(N, 𝔽₂)`** via conjugation, for surjective `ρ`.
A `@[reducible] def` (not an instance); consumers `letI` it. -/
@[reducible] noncomputable def conjModule (hρsurj : Function.Surjective ⇑ρ) :
    DistribMulAction C (H1 ↥(ρ.toMonoidHom.ker : Subgroup Γ) (ZMod 2)) where
  smul c ξ := conjAct ρ (Function.surjInv hρsurj c) ξ
  one_smul ξ := by
    refine (conjAct_ker ρ _ 1 ?_ ξ).trans (conjAct_one ρ ξ)
    rw [Function.surjInv_eq hρsurj, map_one]
  mul_smul c d ξ := by
    show conjAct ρ (Function.surjInv hρsurj (c * d)) ξ
      = conjAct ρ (Function.surjInv hρsurj c) (conjAct ρ (Function.surjInv hρsurj d) ξ)
    rw [← conjAct_comp]
    refine conjAct_ker ρ _ _ ?_ ξ
    rw [map_mul, Function.surjInv_eq hρsurj, Function.surjInv_eq hρsurj,
      Function.surjInv_eq hρsurj]
  smul_zero c := conjAct_zero ρ _
  smul_add c ξ η := conjAct_add ρ _ ξ η

/-- `conjAct` on an `H1mk`-class: the mk-level form of `conjAct_h1ofFun`. -/
theorem conjAct_H1mk (g : Γ) (a : ↥(Z1 ↥(ρ.toMonoidHom.ker : Subgroup Γ) (ZMod 2))) :
    conjAct ρ g (H1mk ↥(ρ.toMonoidHom.ker : Subgroup Γ) (ZMod 2) a)
      = H1mk ↥(ρ.toMonoidHom.ker : Subgroup Γ) (ZMod 2)
          ⟨fun n => a.1 (conjMap ρ g n), comp_conjMap_mem_Z1 ρ a.2 g⟩ := by
  rw [show H1mk ↥(ρ.toMonoidHom.ker : Subgroup Γ) (ZMod 2) a
      = H1ofFun ↥(ρ.toMonoidHom.ker : Subgroup Γ) a.1 from (H1ofFun_of_mem a.2).symm,
    conjAct_h1ofFun ρ g a.2, H1ofFun_of_mem (comp_conjMap_mem_Z1 ρ a.2 g)]

end Conjugation

/-! ## §2 The coefficient bridge `𝔽₂ ≃+ Hom(𝔽₂, μ₂)` -/

section CoefficientBridge

/-- **The coefficient bridge** `𝔽₂ ≃+ Hom(𝔽₂, μ₂)`: `a ↦ (m ↦ μ₂-lift of a·m)`.  Feeds
`H1congr` to move `H¹(N, 𝔽₂)`-classes into the duality bundle's `MuDual`-slot. -/
noncomputable def zmodMuDualEquiv : ZMod 2 ≃+ MuDual 2 (ZMod 2) where
  toFun a :=
    (LocalLiftingDuality.muNTwoEquiv.symm.toAddMonoidHom.comp
      (AddMonoidHom.mk' (fun m => a * m) (fun x y => mul_add a x y)) : ZMod 2 →+ MuN 2)
  invFun φ := LocalLiftingDuality.muNTwoEquiv (φ 1)
  left_inv a := by
    show LocalLiftingDuality.muNTwoEquiv (LocalLiftingDuality.muNTwoEquiv.symm (a * 1)) = a
    rw [AddEquiv.apply_symm_apply, mul_one]
  right_inv φ := by
    refine MuDual.ext 2 (ZMod 2) (fun m => ?_)
    show LocalLiftingDuality.muNTwoEquiv.symm (LocalLiftingDuality.muNTwoEquiv (φ 1) * m) = φ m
    have hz : ∀ b : ZMod 2, b = 0 ∨ b = 1 := by decide
    rcases hz m with rfl | rfl
    · rw [mul_zero, map_zero, map_zero]
    · rw [mul_one, AddEquiv.symm_apply_apply]
  map_add' a b := by
    refine MuDual.ext 2 (ZMod 2) (fun m => ?_)
    show LocalLiftingDuality.muNTwoEquiv.symm ((a + b) * m)
      = (LocalLiftingDuality.muNTwoEquiv.symm (a * m)
        + LocalLiftingDuality.muNTwoEquiv.symm (b * m))
    rw [add_mul, map_add]

/-- Equivariance of the coefficient bridge over any group (both actions are trivial). -/
theorem zmodMuDualEquiv_equivariant {G : Type} [Group G] [DistribMulAction G (ZMod 2)]
    [DistribMulAction G (MuN 2)] (g : G) (a : ZMod 2) :
    zmodMuDualEquiv (g • a) = g • zmodMuDualEquiv a := by
  have htriv : g • zmodMuDualEquiv a = zmodMuDualEquiv a := by
    refine MuDual.ext 2 (ZMod 2) (fun m => ?_)
    rw [muDual_smul_apply, smul_muTwo, smul_zmodTwo]
  rw [htriv, smul_zmodTwo]

end CoefficientBridge

/-! ## §3 The pairing and its nondegeneracy (B6 `perfect11`) -/

section Pairing

variable {Γ : Type} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
  [DistribMulAction Γ (ZMod 2)] [ContinuousSMul Γ (ZMod 2)]
  [DistribMulAction Γ (MuN 2)] [ContinuousSMul Γ (MuN 2)]
variable {C : Type} [Group C] [TopologicalSpace C]
variable (ρ : ContinuousMonoidHom Γ C)
  (D : TateDualityG ↥(ρ.toMonoidHom.ker : Subgroup Γ) 2)

/-- **The Tate pairing at the splitting group** on `M = H¹(N, 𝔽₂)`, `N = ker ρ`: transport the
left argument through the coefficient bridge, cup with the evaluation pairing, and read off
through the bundle's invariant map — `B(x, y) := inv_N(x′ ∪ y)`. -/
noncomputable def pairingK :
    H1 ↥(ρ.toMonoidHom.ker : Subgroup Γ) (ZMod 2)
      →+ H1 ↥(ρ.toMonoidHom.ker : Subgroup Γ) (ZMod 2) →+ ZMod 2 where
  toFun x :=
    D.inv.toAddMonoidHom.comp
      ((cup11 (muDualPairing 2 (ZMod 2)) (muDualPairing_equivariant 2 (ZMod 2)))
        (H1congr zmodMuDualEquiv zmodMuDualEquiv_equivariant x))
  map_zero' := by rw [map_zero, map_zero, AddMonoidHom.comp_zero]
  map_add' x y := by rw [map_add, map_add, AddMonoidHom.comp_add]

/-- **(H2) Nondegeneracy** — the `(1,1)`-perfectness clause of B6 at `N`: a class pairing
trivially with everything is zero. -/
theorem pairingK_nondeg (x : H1 ↥(ρ.toMonoidHom.ker : Subgroup Γ) (ZMod 2))
    (hx : ∀ y, pairingK ρ D x y = 0) : x = 0 := by
  have hperf := D.perfect11 (ZMod 2) (by decide)
  have h0 : D.inv.toAddMonoidHom.comp
      ((cup11 (muDualPairing 2 (ZMod 2)) (muDualPairing_equivariant 2 (ZMod 2)))
        (H1congr zmodMuDualEquiv zmodMuDualEquiv_equivariant x))
      = D.inv.toAddMonoidHom.comp
        ((cup11 (muDualPairing 2 (ZMod 2)) (muDualPairing_equivariant 2 (ZMod 2)))
          (0 : H1 ↥(ρ.toMonoidHom.ker : Subgroup Γ) (MuDual 2 (ZMod 2)))) := by
    ext y
    rw [map_zero, AddMonoidHom.comp_zero]
    exact hx y
  rw [← AddEquiv.symm_apply_apply
    (H1congr zmodMuDualEquiv (zmodMuDualEquiv_equivariant (G := ↥(ρ.toMonoidHom.ker :
      Subgroup Γ)))) x, hperf.1 h0, map_zero]

end Pairing

/-! ## §4 Conjugation invariance of the pairing -/

section Invariance

variable {Γ : Type} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
  [DistribMulAction Γ (ZMod 2)] [ContinuousSMul Γ (ZMod 2)]
  [DistribMulAction Γ (MuN 2)] [ContinuousSMul Γ (MuN 2)]
variable {C : Type} [Group C] [TopologicalSpace C]
variable (ρ : ContinuousMonoidHom Γ C)

omit [DistribMulAction Γ (ZMod 2)] [ContinuousSMul Γ (ZMod 2)] [ContinuousSMul Γ (MuN 2)] in
/-- **Coboundary transport along conjugation**: precomposition with `conjMap × conjMap` carries
`B²(N, μ₂)` into itself (`δ¹ψ ↦ δ¹(ψ ∘ conjMap)`; the coefficient action is trivial). -/
theorem comp_conjMap_mem_B2 (g : Γ)
    {f : ↥(ρ.toMonoidHom.ker : Subgroup Γ) × ↥(ρ.toMonoidHom.ker : Subgroup Γ) → MuN 2}
    (hf : f ∈ B2 ↥(ρ.toMonoidHom.ker : Subgroup Γ) (MuN 2)) :
    (fun p => f (conjMap ρ g p.1, conjMap ρ g p.2))
      ∈ B2 ↥(ρ.toMonoidHom.ker : Subgroup Γ) (MuN 2) := by
  obtain ⟨ψ, hψ, rfl⟩ := hf
  refine ⟨ψ ∘ conjMap ρ g, (mem_C1_iff.mp hψ).comp (continuous_conjMap ρ g), ?_⟩
  funext p
  show p.1 • ψ (conjMap ρ g p.2) - ψ (conjMap ρ g (p.1 * p.2)) + ψ (conjMap ρ g p.1)
      = conjMap ρ g p.1 • ψ (conjMap ρ g p.2)
        - ψ (conjMap ρ g p.1 * conjMap ρ g p.2) + ψ (conjMap ρ g p.1)
  rw [smul_muTwo, smul_muTwo, conjMap_mul_apply]

omit [DistribMulAction Γ (ZMod 2)] [ContinuousSMul Γ (ZMod 2)] [ContinuousSMul Γ (MuN 2)] in
/-- The two-sided form: precomposition with `conjMap × conjMap` preserves `B²` in both
directions. -/
theorem comp_conjMap_mem_B2_iff (g : Γ)
    {f : ↥(ρ.toMonoidHom.ker : Subgroup Γ) × ↥(ρ.toMonoidHom.ker : Subgroup Γ) → MuN 2} :
    ((fun p => f (conjMap ρ g p.1, conjMap ρ g p.2))
        ∈ B2 ↥(ρ.toMonoidHom.ker : Subgroup Γ) (MuN 2))
      ↔ f ∈ B2 ↥(ρ.toMonoidHom.ker : Subgroup Γ) (MuN 2) := by
  refine ⟨fun h => ?_, comp_conjMap_mem_B2 ρ g⟩
  have h' := comp_conjMap_mem_B2 ρ g⁻¹ h
  have hfun : (fun p : ↥(ρ.toMonoidHom.ker : Subgroup Γ)
        × ↥(ρ.toMonoidHom.ker : Subgroup Γ) =>
      f (conjMap ρ g (conjMap ρ g⁻¹ p.1), conjMap ρ g (conjMap ρ g⁻¹ p.2))) = f := by
    funext p
    rw [conjMap_conjMap_inv, conjMap_conjMap_inv]
  rwa [hfun] at h'

variable (D : TateDualityG ↥(ρ.toMonoidHom.ker : Subgroup Γ) 2)

omit [DistribMulAction Γ (ZMod 2)] [ContinuousSMul Γ (ZMod 2)] in
/-- The invariant map kills conjugation: `ZMod 2`-valued, so it suffices that the two classes
vanish together — and vanishing is `B²`-membership, transported by `comp_conjMap_mem_B2_iff`. -/
theorem inv_H2mk_eq_of_comp_conjMap (g : Γ)
    (Fc F : ↥(Z2 ↥(ρ.toMonoidHom.ker : Subgroup Γ) (MuN 2)))
    (hco : Fc.1 = fun p => F.1 (conjMap ρ g p.1, conjMap ρ g p.2)) :
    D.inv (H2mk ↥(ρ.toMonoidHom.ker : Subgroup Γ) (MuN 2) Fc)
      = D.inv (H2mk ↥(ρ.toMonoidHom.ker : Subgroup Γ) (MuN 2) F) := by
  have h2 : ∀ u v : ZMod 2, (u = 0 ↔ v = 0) → u = v := by decide
  have hiv : ∀ W : H2 ↥(ρ.toMonoidHom.ker : Subgroup Γ) (MuN 2), D.inv W = 0 ↔ W = 0 :=
    fun _ => map_eq_zero_iff _ D.inv.injective
  have hz : ∀ W : ↥(Z2 ↥(ρ.toMonoidHom.ker : Subgroup Γ) (MuN 2)),
      (H2mk ↥(ρ.toMonoidHom.ker : Subgroup Γ) (MuN 2) W = 0)
        ↔ W.1 ∈ B2 ↥(ρ.toMonoidHom.ker : Subgroup Γ) (MuN 2) := fun W =>
    (QuotientAddGroup.eq_zero_iff W).trans AddSubgroup.mem_addSubgroupOf
  refine h2 _ _ ?_
  rw [hiv, hiv, hz, hz, hco]
  exact comp_conjMap_mem_B2_iff ρ g

/-- **(H1) Conjugation invariance of the pairing**: `B(g·x, g·y) = B(x, y)` for the
`conjAct`-action of any `g : Γ`. -/
theorem pairingK_conjAct (g : Γ) (x y : H1 ↥(ρ.toMonoidHom.ker : Subgroup Γ) (ZMod 2)) :
    pairingK ρ D (conjAct ρ g x) (conjAct ρ g y) = pairingK ρ D x y := by
  obtain ⟨a, rfl⟩ := H1mk_surjective x
  obtain ⟨b, rfl⟩ := H1mk_surjective y
  rw [conjAct_H1mk, conjAct_H1mk]
  show D.inv
      ((cup11 (muDualPairing 2 (ZMod 2)) (muDualPairing_equivariant 2 (ZMod 2)))
        (H1congr zmodMuDualEquiv zmodMuDualEquiv_equivariant
          (H1mk _ _ ⟨fun n => a.1 (conjMap ρ g n), comp_conjMap_mem_Z1 ρ a.2 g⟩))
        (H1mk _ _ ⟨fun n => b.1 (conjMap ρ g n), comp_conjMap_mem_Z1 ρ b.2 g⟩))
    = D.inv
      ((cup11 (muDualPairing 2 (ZMod 2)) (muDualPairing_equivariant 2 (ZMod 2)))
        (H1congr zmodMuDualEquiv zmodMuDualEquiv_equivariant (H1mk _ _ a)) (H1mk _ _ b))
  rw [H1congr_mk, H1congr_mk, cup11_mk_mk, cup11_mk_mk]
  refine inv_H2mk_eq_of_comp_conjMap ρ D g _ _ (funext fun p => ?_)
  -- the two cup cocycles agree pointwise once the (trivial) `𝔽₂`-actions are collapsed
  show muDualPairing 2 (ZMod 2) (zmodMuDualEquiv (a.1 (conjMap ρ g p.1)))
      (p.1 • b.1 (conjMap ρ g p.2))
    = muDualPairing 2 (ZMod 2) (zmodMuDualEquiv (a.1 (conjMap ρ g p.1)))
      (conjMap ρ g p.1 • b.1 (conjMap ρ g p.2))
  rw [smul_zmodTwo, smul_zmodTwo]

/-- **(H1) in `conjModule` form** — the literal `hBinv` hypothesis of the abstract `hduality`
engine `GQ2.card_equivHoms_deep_eq_quot`. -/
theorem pairingK_conjModule (hρsurj : Function.Surjective ⇑ρ) (c : C)
    (x y : H1 ↥(ρ.toMonoidHom.ker : Subgroup Γ) (ZMod 2)) :
    letI := conjModule ρ hρsurj
    pairingK ρ D (c • x) (c • y) = pairingK ρ D x y := by
  letI := conjModule ρ hρsurj
  exact pairingK_conjAct ρ D _ x y

end Invariance

/-! ## §5 The bundle at the splitting group

`GQ2.ker_isLocalDualizingGroup` (`GQ2/DeepDualityK.lean` :70) covers `ker ρ ≤ G_ℚ₂` only.  The
dyadic tower needs `N_K = ker ρ ≤ G_K = ↥U ≤ G_ℚ₂`, so the statement is generalized to any local
dualizing `Γ` through `isLocalDualizingGroup_of_openEmbedding` (`GQ2/Dyadic/LocalGauss/Q0.lean`
§6). -/

section KernelBundle

variable {Γ : Type} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
  [DistribMulAction Γ (MuN 2)]
variable {C : Type} [Group C] [TopologicalSpace C] [DiscreteTopology C] [Finite C]
variable (ρ : ContinuousMonoidHom Γ C)

omit [IsTopologicalGroup Γ] [DistribMulAction Γ (MuN 2)] [Finite C] in
/-- `ker ρ` is open when `C` is discrete. -/
theorem isOpen_ker : IsOpen ((ρ.toMonoidHom.ker : Subgroup Γ) : Set Γ) := by
  change IsOpen (ρ ⁻¹' ({1} : Set C))
  exact (isOpen_discrete ({1} : Set C)).preimage ρ.continuous_toFun

omit [IsTopologicalGroup Γ] in
/-- **`ker ρ` is a local dualizing group whenever `Γ` is** — the subtype embedding is open with
finite-index image (the quotient injects into the finite `C`), and the `μ₂`-action is
restriction.  Generalizes `GQ2.ker_isLocalDualizingGroup` from `Γ = G_ℚ₂` to the nested tower
`N_K ≤ G_K ≤ G_ℚ₂`. -/
theorem ker_isLocalDualizingGroup (hΓ : IsLocalDualizingGroup Γ 2) :
    IsLocalDualizingGroup ↥(ρ.toMonoidHom.ker : Subgroup Γ) 2 := by
  refine isLocalDualizingGroup_of_openEmbedding hΓ (ρ.toMonoidHom.ker).subtype
    (isOpen_ker ρ).isOpenEmbedding_subtypeVal ?_ (fun _ _ => rfl)
  rw [Subgroup.range_subtype]
  haveI : Finite (Γ ⧸ (ρ.toMonoidHom.ker : Subgroup Γ)) :=
    Finite.of_injective _ (QuotientGroup.quotientKerEquivRange ρ.toMonoidHom).injective
  exact Subgroup.finiteIndex_of_finite_quotient

variable [ContinuousSMul Γ (MuN 2)]

/-- **The Tate-duality bundle at the splitting group** — the base-generalized B6 axiom
`GQ2.tateDualityAt` at `N = ker ρ`, for any local dualizing ambient `Γ`. -/
noncomputable def tateDualityKer (hΓ : IsLocalDualizingGroup Γ 2) :
    TateDualityG ↥(ρ.toMonoidHom.ker : Subgroup Γ) 2 :=
  tateDualityAt ↥(ρ.toMonoidHom.ker : Subgroup Γ) 2 (ker_isLocalDualizingGroup ρ hΓ)

end KernelBundle

end GQ2.Dyadic
