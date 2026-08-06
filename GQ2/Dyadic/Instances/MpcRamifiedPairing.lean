/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Opus-5
-/
import GQ2.Dyadic.Instances.MpcPairings

/-!
# The fully general Heisenberg laws, and the ramified procyclic-`M` row

`EvenHeisPure` carries the second-order product, conjugation and commutator laws under a
*triviality* hypothesis on one of the two bases: `heisMul_of_trivial_left`,
`heisConjR_of_trivial`, `heisCommR_of_trivial` and — the sharpest of them —
`heisCommR_of_trivial_right`, which needs only the **right** factor's base to act trivially.

That is enough for the compact-`M` ramified row, where the right entry of the one live commutator
`[A₀, x₁]` is a bare wild letter.  It is **not** enough for the corrected procyclic-`M` row: on
the ramified reading `hS₂` is gone, so

```
A = x₀⁻¹C₀^{−m}   acts by   S₂^{−sm},        B = x₁σ₂^{p}   acts by   S₂^{p},
```

and neither base is trivial.  This file therefore proves the laws with **no hypothesis at all**
on either base, and reads the ramified row off them.

## The general commutator law

For `p = (a, λ, z, g)` and `r = (b, μ, w, k)` in `H(A) ⋊ C`, `commR p r = p⁻¹r⁻¹pr` has

```
jet     :  −g⁻¹a − g⁻¹k⁻¹b + g⁻¹k⁻¹a + g⁻¹k⁻¹g b            (and the same on λ, μ)
centre  :  λ(a) + μ(b) + λ(k⁻¹b) + λ(k⁻¹a) + μ(a) + λ(k⁻¹gb) + μ(gb) + λ(gb)
base    :  commR g k
```

the centre being read in `ZMod 2`, where signs are invisible.  At `k = 1` — more precisely
whenever `k` acts trivially — four of the eight central terms cancel in pairs and the remaining
four are `heisCommR_of_trivial_right`'s `μ(b) + λ(b) + μ(a) + μ(gb)`; `heisCommR_general_right`
below rederives that specialization from the general law, which is the law's own regression test.

The companion laws `heisSq_general` (`p²`) and `heisConjR_general` (`p^q`) are proved the same
way and are the other two arbitrary-base primitives the procyclic-`M` row needs: its live
factors are `A²`, `[A,B]` and `E₀₁^pc` (a nest of conjugations), plus their hat twins.
-/

namespace GQ2.Dyadic

noncomputable section

open GQ2 GQ2.FoxH

section GeneralLaws

variable {C : Type*} [Group C] {A : Type*} [AddCommGroup A] [DistribMulAction C A]

/-- **The general square.**  No hypothesis: the jets are `a + g·a`, `λ + g·λ` and the centre is
the single cross term `λ(g·a)` — the two copies of `p.z` cancel in `ZMod 2`. -/
theorem heisSq_general (p : HeisLift A C) :
    p * p = ⟨p.a + p.g • p.a, p.l + p.g • p.l, p.l (p.g • p.a), p.g * p.g⟩ := by
  refine HeisLift.ext rfl rfl ?_ rfl
  show p.z + p.z + p.l (p.g • p.a) = p.l (p.g • p.a)
  rw [CharTwo.add_self_eq_zero, zero_add]

/-- **The general conjugation law** `p^q = q⁻¹pq`, with no hypothesis on either base. -/
theorem heisConjR_general (p q : HeisLift A C) :
    conjR p q = ⟨-(q.g⁻¹ • q.a) + q.g⁻¹ • p.a + q.g⁻¹ • (p.g • q.a),
      -(q.g⁻¹ • q.l) + q.g⁻¹ • p.l + q.g⁻¹ • (p.g • q.l),
      p.z + q.l q.a + q.l p.a + q.l (p.g • q.a) + p.l (p.g • q.a),
      conjR p.g q.g⟩ := by
  rw [conjR]
  refine HeisLift.ext ?_ ?_ ?_ ?_
  · simp only [HeisLift.mul_a, HeisLift.inv_a, HeisLift.mul_g, HeisLift.inv_g, mul_smul]
  · simp only [HeisLift.mul_l, HeisLift.inv_l, HeisLift.mul_g, HeisLift.inv_g, mul_smul]
  · simp only [HeisLift.mul_z, HeisLift.mul_l, HeisLift.mul_g, HeisLift.inv_z,
      HeisLift.inv_l, HeisLift.inv_g, mul_smul, inv_inv,
      ElemDual.add_apply, ElemDual.neg_apply, ElemDual.smul_apply, smul_inv_smul]
    generalize p.z = c₁
    generalize q.z = c₂
    generalize q.l q.a = c₃
    generalize q.l p.a = c₄
    generalize q.l (p.g • q.a) = c₅
    generalize p.l (p.g • q.a) = c₆
    revert c₁ c₂ c₃ c₄ c₅ c₆
    decide
  · simp only [HeisLift.mul_g, HeisLift.inv_g]
    rfl

/-- **The fully general commutator law** — the central statement of this file.  No hypothesis on
either base; `heisCommR_of_trivial_right` is the special case in which `r.g` acts trivially, and
`heisCommR_of_trivial` the one in which both do. -/
theorem heisCommR_general (p r : HeisLift A C) :
    commR p r = ⟨-(p.g⁻¹ • p.a) - p.g⁻¹ • (r.g⁻¹ • r.a) + p.g⁻¹ • (r.g⁻¹ • p.a)
        + p.g⁻¹ • (r.g⁻¹ • (p.g • r.a)),
      -(p.g⁻¹ • p.l) - p.g⁻¹ • (r.g⁻¹ • r.l) + p.g⁻¹ • (r.g⁻¹ • p.l)
        + p.g⁻¹ • (r.g⁻¹ • (p.g • r.l)),
      p.l p.a + r.l r.a + p.l (r.g⁻¹ • r.a) + p.l (r.g⁻¹ • p.a) + r.l p.a
        + p.l (r.g⁻¹ • (p.g • r.a)) + r.l (p.g • r.a) + p.l (p.g • r.a),
      commR p.g r.g⟩ := by
  rw [commR]
  refine HeisLift.ext ?_ ?_ ?_ ?_
  · simp only [HeisLift.mul_a, HeisLift.inv_a, HeisLift.mul_g, HeisLift.inv_g, mul_smul,
      smul_neg]
    abel
  · simp only [HeisLift.mul_l, HeisLift.inv_l, HeisLift.mul_g, HeisLift.inv_g, mul_smul,
      smul_neg]
    abel
  · simp only [HeisLift.mul_z, HeisLift.mul_l, HeisLift.mul_g, HeisLift.inv_z,
      HeisLift.inv_a, HeisLift.inv_l, HeisLift.inv_g, mul_smul, inv_inv,
      ElemDual.add_apply, ElemDual.neg_apply, ElemDual.smul_apply, map_neg,
      smul_neg, smul_inv_smul]
    generalize p.z = c₁
    generalize r.z = c₂
    generalize p.l p.a = c₃
    generalize r.l r.a = c₄
    generalize p.l (r.g⁻¹ • r.a) = c₅
    generalize p.l (r.g⁻¹ • p.a) = c₆
    generalize r.l p.a = c₇
    generalize p.l (r.g⁻¹ • (p.g • r.a)) = c₈
    generalize r.l (p.g • r.a) = c₉
    generalize p.l (p.g • r.a) = c₁₀
    revert c₁ c₂ c₃ c₄ c₅ c₆ c₇ c₈ c₉ c₁₀
    decide
  · simp only [HeisLift.mul_g, HeisLift.inv_g]
    rfl

/-- **The general law specializes to the one-sided law.**  With `r.g` acting trivially the four
`k⁻¹`-twisted central terms collapse onto their untwisted partners and cancel in pairs, leaving
`heisCommR_of_trivial_right`'s value.  This is the regression test that pins the general law's
eight-term centre. -/
theorem heisCommR_general_right (p r : HeisLift A C) (hr : ∀ a : A, r.g • a = a) :
    commR p r = ⟨r.a - p.g⁻¹ • r.a, r.l - p.g⁻¹ • r.l,
      r.l r.a + p.l r.a + r.l p.a + r.l (p.g • r.a), commR p.g r.g⟩ := by
  have hri : ∀ a : A, r.g⁻¹ • a = a := fun a ↦ inv_smul_eq_iff.mpr (hr a).symm
  have hriD : ∀ lam : ElemDual A, r.g⁻¹ • lam = lam := smul_elemDual_of_trivial hri
  rw [heisCommR_general]
  refine HeisLift.ext ?_ ?_ ?_ rfl
  · show -(p.g⁻¹ • p.a) - p.g⁻¹ • (r.g⁻¹ • r.a) + p.g⁻¹ • (r.g⁻¹ • p.a)
        + p.g⁻¹ • (r.g⁻¹ • (p.g • r.a)) = r.a - p.g⁻¹ • r.a
    rw [hri, hri, hri, inv_smul_smul]
    abel
  · show -(p.g⁻¹ • p.l) - p.g⁻¹ • (r.g⁻¹ • r.l) + p.g⁻¹ • (r.g⁻¹ • p.l)
        + p.g⁻¹ • (r.g⁻¹ • (p.g • r.l)) = r.l - p.g⁻¹ • r.l
    rw [hriD, hriD, hriD, inv_smul_smul]
    abel
  · show p.l p.a + r.l r.a + p.l (r.g⁻¹ • r.a) + p.l (r.g⁻¹ • p.a) + r.l p.a
        + p.l (r.g⁻¹ • (p.g • r.a)) + r.l (p.g • r.a) + p.l (p.g • r.a)
      = r.l r.a + p.l r.a + r.l p.a + r.l (p.g • r.a)
    rw [hri, hri, hri]
    generalize p.l p.a = c₁
    generalize r.l r.a = c₂
    generalize p.l r.a = c₃
    generalize r.l p.a = c₄
    generalize r.l (p.g • r.a) = c₅
    generalize p.l (p.g • r.a) = c₆
    revert c₁ c₂ c₃ c₄ c₅ c₆
    decide

end GeneralLaws

/-! ## Second-order pure words on ramified offsets

`MProcyclicNormal.IsDead` asks for a pure lift **whose base acts trivially**, and the second half
is exactly what the ramified reading has to give up.  `IsPure` drops it: it is membership in the
subgroup `heisTrivial`, so it is closed under every group operation for free, and it needs *no*
hypothesis on the action — only on the offsets. -/

section Pure

variable {X : Type*} {C : Type*} [Group C] {A : Type*} [AddCommGroup A] [DistribMulAction C A]
  (μ : X → C) (x : X → A) (y : X → ElemDual A) (E : Zhat → ℤ) (E₂ : ℤ_[2] → ℤ)

/-- **Second-order pure**: the word denotes `⟨0, 0, 0, G⟩` for some `G`, with no condition
whatever on `G`. -/
def IsPure (w : PWord X) : Prop :=
  heisEvalZ μ x y E E₂ w ∈ Certificates.MCompact.heisTrivial A C

variable {μ x y E E₂}

theorem IsPure.a {w : PWord X} (hw : IsPure μ x y E E₂ w) : (heisEvalZ μ x y E E₂ w).a = 0 := hw.1

theorem IsPure.l {w : PWord X} (hw : IsPure μ x y E E₂ w) :
    (heisEvalZ μ x y E E₂ w).l = 0 := hw.2.1

theorem IsPure.z {w : PWord X} (hw : IsPure μ x y E E₂ w) : (heisEvalZ μ x y E E₂ w).z = 0 :=
  hw.2.2

theorem IsPure.jetZero {w : PWord X} (hw : IsPure μ x y E E₂ w) :
    heisEvalZ μ x y E E₂ w ∈ heisJetZero A C := ⟨hw.1, hw.2.1⟩

/-- A pure word's value **is** the pure lift of its base. -/
theorem IsPure.eq_heisPure {w : PWord X} (hw : IsPure μ x y E E₂ w) :
    heisEvalZ μ x y E E₂ w = heisPure (heisEvalZ μ x y E E₂ w).g :=
  HeisLift.ext hw.1 hw.2.1 hw.2.2 rfl

/-- A dead word is pure; the converse needs the base to act trivially. -/
theorem _root_.GQ2.Dyadic.MProcyclicNormal.IsDead.isPure {w : PWord X}
    (hw : MProcyclicNormal.IsDead μ x y E E₂ w) : IsPure μ x y E E₂ w := by
  obtain ⟨G, hG, -⟩ := hw
  rw [IsPure, hG]
  exact ⟨rfl, rfl, rfl⟩

variable (μ x y E E₂)

theorem isPure_one : IsPure μ x y E E₂ (.one : PWord X) := Subgroup.one_mem _

/-- **The only hypothesis purity ever needs**: the letter's two offsets vanish. -/
theorem isPure_gen {i : X} (hx : x i = 0) (hy : y i = 0) : IsPure μ x y E E₂ (.gen i) := by
  rw [IsPure, heisEvalZ_gen_of_offsets_zero μ x y E E₂ i hx hy]
  exact ⟨rfl, rfl, rfl⟩

variable {μ x y E E₂}

theorem IsPure.mul {u v : PWord X} (hu : IsPure μ x y E E₂ u) (hv : IsPure μ x y E E₂ v) :
    IsPure μ x y E E₂ (.mul u v) := by
  rw [IsPure, heisEvalZ_mul]
  exact Subgroup.mul_mem _ hu hv

theorem IsPure.inv {u : PWord X} (hu : IsPure μ x y E E₂ u) : IsPure μ x y E E₂ (.inv u) := by
  rw [IsPure, heisEvalZ_inv]
  exact Subgroup.inv_mem _ hu

theorem IsPure.zpow {u : PWord X} (hu : IsPure μ x y E E₂ u) (k : ℤ) :
    IsPure μ x y E E₂ (.zpow u k) := by
  rw [IsPure, heisEvalZ_zpow]
  exact Subgroup.zpow_mem _ hu k

theorem IsPure.profPow {u : PWord X} (hu : IsPure μ x y E E₂ u) (γ : Zhat) :
    IsPure μ x y E E₂ (.profPow u γ) := by
  rw [IsPure, heisEvalZ_profPow]
  exact Subgroup.zpow_mem _ hu _

/-- ⚠ Unlike `IsDead.conj`, the conjugator must be pure too: `heisTrivial` is not normal, and a
conjugate of a pure lift by a lift with a nonzero jet has a nonzero jet
(`heisConjR_general`). -/
theorem IsPure.conj {u g : PWord X} (hu : IsPure μ x y E E₂ u) (hg : IsPure μ x y E E₂ g) :
    IsPure μ x y E E₂ (.conj u g) := by
  rw [IsPure, heisEvalZ_conj, conjR]
  exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ hg) hu) hg

@[inherit_doc IsPure.conj]
theorem IsPure.comm {u v : PWord X} (hu : IsPure μ x y E E₂ u) (hv : IsPure μ x y E E₂ v) :
    IsPure μ x y E E₂ (.comm u v) := by
  rw [IsPure, heisEvalZ_comm, commR]
  exact Subgroup.mul_mem _
    (Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ hu) (Subgroup.inv_mem _ hv)) hu) hv

theorem isPure_prodList {l : List (PWord X)} (hl : ∀ w ∈ l, IsPure μ x y E E₂ w) :
    IsPure μ x y E E₂ (PWord.prodList l) := by
  induction l with
  | nil => exact isPure_one μ x y E E₂
  | cons w ws ih =>
      rw [PWord.prodList_cons]
      exact (hl w List.mem_cons_self).mul (ih fun u hu ↦ hl u (List.mem_cons_of_mem _ hu))

end Pure

/-! ## The pure factors of the ramified procyclic-`M` row

On even normal offsets the vanishing set is `{σ, τ, x₂}`, and **every** letter of the row built
only out of those three is pure — with no hypothesis on the action, so the classification is the
same on the ramified reading as on the unramified one.  That covers

```
C₀ = x₂σ₂^s,   Ĉ₀ = σ₂^s,   D = σ^{η̂},   δ₂,   z = δ₂δ₂^{σ₂^p},   E₂^pc,
```

hence the four factors `C₀^{2^α}`, `[C₀,D]`, `Ĉ₀^{2^α}`, `[Ĉ₀,D]` and the factor `E₂^pc`.

What is **not** covered, and what therefore is the ramified row's live set, is
`A² · [A,B] · E₀₁^pc` in the linear copy, `Â² · [Â,B̂] · Ê₀₁^pc` in the hat copy, and the plus
block `δ₀²[δ₀,δ₁]` — because `δ₀` and `δ₁` carry the two surviving offsets `d₀`, `d₁`.  On the
*unramified* reading the six hat-copy and plus-block factors die for a different reason (the
`δ`-letters are `heisTrivial` once `τ` acts trivially, `MProcyclicNormal.isDead_dW`); that reason
is exactly what the ramified reading removes. -/

section RamPure

variable {h : ℕ} {C : Type*} [Group C] {A : Type*} [AddCommGroup A] [DistribMulAction C A]
  (t : Marking (2 + 2 * h) C) (x : Generator (2 + 2 * h) → A)
  (y : Generator (2 + 2 * h) → ElemDual A) (E : Zhat → ℤ) (E₂ : ℤ_[2] → ℤ)

open GQ2.Dyadic.Words GQ2.Dyadic.Words.Mpc

variable (hxσ : x .sigma = 0) (hyσ : y .sigma = 0) (hxτ : x .tau = 0) (hyτ : y .tau = 0)
  (hx2 : x (coreLetter h 2) = 0) (hy2 : y (coreLetter h 2) = 0)

include hxσ hyσ in
theorem isPure_sigma : IsPure ⇑t x y E E₂ (.gen (Generator.sigma : Generator (2 + 2 * h))) :=
  isPure_gen _ _ _ _ _ hxσ hyσ

include hxσ hyσ in
theorem isPure_sigma2W : IsPure ⇑t x y E E₂ (sigma2W : PWord (Generator (2 + 2 * h))) :=
  (isPure_sigma t x y E E₂ hxσ hyσ).profPow _

include hxσ hyσ in
theorem isPure_sig2PowW (k : ℕ) : IsPure ⇑t x y E E₂ (sig2PowW h k) := by
  match k with
  | 0 => exact (isPure_sigma2W t x y E E₂ hxσ hyσ).zpow _
  | 1 => exact isPure_sigma2W t x y E E₂ hxσ hyσ
  | (j + 2) => exact (isPure_sigma2W t x y E E₂ hxσ hyσ).zpow _

include hxσ hyσ in
/-- **Every display is pure**: all three constructors are `σ`-powers. -/
theorem isPure_display (η : EtaDisplay) : IsPure ⇑t x y E E₂ (η.toPWord (n := 2 + 2 * h)) := by
  have hσ := isPure_sigma t x y E E₂ hxσ hyσ
  cases η with
  | one => exact hσ
  | lit k => exact hσ.zpow k
  | hat num den => exact hσ.profPow _

include hxσ hyσ hx2 hy2 in
theorem isPure_c0W (s' : ℕ) : IsPure ⇑t x y E E₂ (c0W h s') := by
  refine isPure_prodList fun w hw ↦ ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl
  · exact isPure_gen _ _ _ _ _ hx2 hy2
  · exact (isPure_sigma2W t x y E E₂ hxσ hyσ).zpow _

include hxσ hyσ in
theorem isPure_c0HatW (s' : ℕ) : IsPure ⇑t x y E E₂ (c0HatW h s') :=
  (isPure_sigma2W t x y E E₂ hxσ hyσ).zpow _

include hxτ hyτ hx2 hy2 in
/-- **`δ₂` is pure on ramified offsets**, with no hypothesis on the action: both letters of
`u₂ = (x₂τ)^{ω₂}` carry zero offsets. -/
theorem isPure_dW2 : IsPure ⇑t x y E E₂ (dW h 2) := by
  have hx2' : IsPure ⇑t x y E E₂ (.gen (coreLetter h 2)) := isPure_gen _ _ _ _ _ hx2 hy2
  have hτ' : IsPure ⇑t x y E E₂ (.gen (Generator.tau : Generator (2 + 2 * h))) :=
    isPure_gen _ _ _ _ _ hxτ hyτ
  refine isPure_prodList fun w hw ↦ ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl
  · refine IsPure.profPow (isPure_prodList fun u hu ↦ ?_) _
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
    rcases hu with rfl | rfl
    · exact hx2'
    · exact hτ'
  · exact hx2'.inv

include hxσ hyσ hxτ hyτ hx2 hy2 in
theorem isPure_zW (pp : ℕ) : IsPure ⇑t x y E E₂ (zW h pp) := by
  have hd2 := isPure_dW2 t x y E E₂ hxτ hyτ hx2 hy2
  match pp with
  | 0 => exact hd2.zpow _
  | (j + 1) =>
      refine isPure_prodList fun w hw ↦ ?_
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
      rcases hw with rfl | rfl
      · exact hd2
      · exact hd2.conj (isPure_sig2PowW t x y E E₂ hxσ hyσ _)

include hxσ hyσ hxτ hyτ hx2 hy2 in
/-- **The whole orbit-norm block `E₂^pc` is pure** — every letter in it is a `δ₂` or a
`σ₂`-power. -/
theorem isPure_e2W (s' mm pp : ℕ) : IsPure ⇑t x y E E₂ (e2W h s' mm pp) := by
  have hd2 := isPure_dW2 t x y E E₂ hxτ hyτ hx2 hy2
  have hz := isPure_zW t x y E E₂ hxσ hyσ hxτ hyτ hx2 hy2 pp
  have hs := (isPure_sigma2W t x y E E₂ hxσ hyσ).zpow (s' : ℤ)
  refine isPure_prodList fun w hw ↦ ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl
  · exact hd2.conj hs
  · refine IsPure.conj (isPure_prodList fun u hu ↦ ?_)
      ((isPure_sigma2W t x y E E₂ hxσ hyσ).zpow _)
    rw [Export.orbitNormFactors, List.mem_map] at hu
    obtain ⟨j, -, rfl⟩ := hu
    exact hz.conj (hs.zpow _)

include hxσ hyσ hxτ hyτ hx2 hy2 in
/-- **The pure factors of the ramified procyclic-`M` row, exhaustively.**

Five of the eleven displayed factors of `R_lin^pc · R̂^pc` are pure on even normal offsets with
no hypothesis on the action: the two `C₀`-powers, the two `[·, D]` commutators and the
orbit-norm block `E₂^pc`.  Everything else — `A²`, `[A,B]`, `E₀₁^pc`, their hat twins `Â²`,
`[Â,B̂]`, `Ê₀₁^pc`, and the plus block `δ₀²[δ₀,δ₁]` — carries one of the two surviving offsets
`d₀`, `d₁` and is genuinely live.

⚠ The plus block is live too.  On the unramified reading it dies with the rest of the
`δ`-letters (`MProcyclicNormal.isDead_dW`, which needs `τ` to act trivially); on the ramified
reading nothing kills it, because `δ₀` and `δ₁` are built on `x₀` and `x₁`. -/
theorem isPure_mpcW_factor (α r pp : ℕ) (η : EtaDisplay)
    {w : PWord (Generator (2 + 2 * h))}
    (hw : w ∈ [PWord.zpow (c0W h (s r)) (((2 : ℕ) ^ α : ℕ) : ℤ),
               PWord.comm (c0W h (s r)) (η.toPWord (n := 2 + 2 * h)),
               e2W h (s r) (m α) pp,
               PWord.zpow (c0HatW h (s r)) (((2 : ℕ) ^ α : ℕ) : ℤ),
               PWord.comm (c0HatW h (s r)) (η.toPWord (n := 2 + 2 * h))]) :
    IsPure ⇑t x y E E₂ w := by
  have hc0 := isPure_c0W t x y E E₂ hxσ hyσ hx2 hy2 (s r)
  have hc0h := isPure_c0HatW t x y E E₂ hxσ hyσ (s r)
  have hD := isPure_display t x y E E₂ hxσ hyσ η
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl | rfl | rfl
  · exact hc0.zpow _
  · exact hc0.comm hD
  · exact isPure_e2W t x y E E₂ hxσ hyσ hxτ hyτ hx2 hy2 _ _ _
  · exact hc0h.zpow _
  · exact hc0h.comm hD

end RamPure

end

end GQ2.Dyadic

/-! ## Axiom audit -/

section AxiomAudit

#print axioms GQ2.Dyadic.heisSq_general
#print axioms GQ2.Dyadic.heisConjR_general
#print axioms GQ2.Dyadic.heisCommR_general
#print axioms GQ2.Dyadic.heisCommR_general_right
#print axioms GQ2.Dyadic.MProcyclicNormal.IsDead.isPure
#print axioms GQ2.Dyadic.isPure_gen
#print axioms GQ2.Dyadic.IsPure.mul
#print axioms GQ2.Dyadic.IsPure.inv
#print axioms GQ2.Dyadic.IsPure.zpow
#print axioms GQ2.Dyadic.IsPure.profPow
#print axioms GQ2.Dyadic.IsPure.conj
#print axioms GQ2.Dyadic.IsPure.comm
#print axioms GQ2.Dyadic.isPure_prodList
#print axioms GQ2.Dyadic.isPure_sigma2W
#print axioms GQ2.Dyadic.isPure_sig2PowW
#print axioms GQ2.Dyadic.isPure_display
#print axioms GQ2.Dyadic.isPure_c0W
#print axioms GQ2.Dyadic.isPure_c0HatW
#print axioms GQ2.Dyadic.isPure_dW2
#print axioms GQ2.Dyadic.isPure_zW
#print axioms GQ2.Dyadic.isPure_e2W
#print axioms GQ2.Dyadic.isPure_mpcW_factor

end AxiomAudit
