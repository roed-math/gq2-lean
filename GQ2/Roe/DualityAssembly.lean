/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Opus-4.8 and Fable-5
-/
module

public import GQ2.Roe.NormalForms
public import GQ2.Roe.Hessian
public import GQ2.Roe.DevissageInduction
public import GQ2.DualityAssembly
public import GQ2.LocalLiftingDuality

@[expose] public section

/-!
# Assembling `prop_5_15_R` (candidate deformation duality) on the `r_R` spine  (⟦prop:duality⟧)

`prop_5_15_R : IsSelfDual_R t A` for every finite elementary `𝔽₂[C]`-module — the Roe note's
Candidate deformation duality ⟦prop:duality⟧, the `Γ_R` twin of `GQ2/DualityAssembly.lean`.
Route exactly as `Γ_A`: the simple modules are self-dual (`selfDual_of_simple_R` — trivial module
via R25's `trivialSelfDual_R`; nontrivial simples via the ⟦lem:normalforms⟧ normal forms + the
⟦prop:hessian⟧ degree-one pairing), then the dévissage strong induction `prop_5_15_of_simple_R`
(`GQ2/Roe/DevissageInduction.lean`, two-out-of-three `lemma_5_11_R` along a composition series).

## The `x₀ ↔ x₁` wild-column swap

The tame relator is shared with `Γ_A`, but the two wild columns are interchanged
(`GQ2.Roe.WildRow`): the split `Z¹_R` shape is `x 1 = 0 ∧ x 2 = 0` (`Γ_A`: `x 1 = 0 ∧ x 3 = 0`)
and the normal form is **`x₁`-supported** `(0,0,0,d)` (`x1Supported`, slot `x 3`; `Γ_A`:
`x0Supported`, slot `x 2`).  Two signature deltas against the `Γ_A` twins, both from
`GQ2.Roe.NormalForms`/`GQ2.Roe.Hessian`:

* the split *shapes* need **no `σ₂`-tameness `hU`** (`σ₂` is only a conjugator in `r_R`;
  `split_shapes_of_wild_R` drops `Γ_A` `split_shapes_of_wild`'s `hU`) — the split *pairing*
  `mixedB_R_pairing_split` still consumes `hU`, derived as in `Γ_A` from `sigma2_smul_trivial`;
* the ramified pairing lemmas carry no `ht`/`hw` arguments (`mixedB_R_pairing_ramified`).

Word-free ingredients are **reused unsuffixed** from the `Γ_A` assembly, never cloned:
`card_H0w_eq_one_of_nontrivial`, `card_fixedPts_elemDual_eq_one_of_nontrivial`,
`tau_split_or_ramified`, `elemDual_smul_trivial_of` (`GQ2.DualityAssembly`), the tame
representation-theory providers (`GQ2.TameSimple`), `H0w_eq_fixedPts` and `elemDual_separates`
(`GQ2.Devissage`).

## Card bookkeeping for the simple case

For a nontrivial simple module the invariants `H⁰w(A) = A^C` vanish, so the normal form
`H¹_R ≅ A` forces `#Z¹_R = #A²` and `#H²_R = 1` — clauses 1 and 2 of `IsSelfDual_R` (via the
Euler characteristic `card_H1w_eq_R` / rank-nullity `card_Z1w_eq_sq_mul_card_H2w_R`).

## Corollary 5.17 numerics (`cor_5_17_card_R`)

"Comparison with the local complex then uses local Tate duality as in [RT Prop. 5.16 and
Cor. 5.17]" (⟦prop:duality⟧'s proof): the word-generic local half `prop_5_16`
(`GQ2/LocalLiftingDuality.lean`) is **reused verbatim** — it never mentions the marking word —
so the corollary is a thin splice of `prop_5_15_R` (clauses 1–2) against `prop_5_16`'s
display-(57) numerics.
-/

namespace GQ2

namespace FoxH

open scoped Classical

section Assembly

variable {C : Type*} [Group C] [Finite C] {A : Type*} [AddCommGroup A] [Finite A]
  [DistribMulAction C A]

/-- **`H¹_R ≅ A` from the normal form**: when every `x₁`-supported tuple is a Roe cocycle and
every cocycle is uniquely `x₁`-supported modulo coboundaries (⟦lem:normalforms⟧), the class map
`A → H¹_R`, `d ↦ [x1Supported d]`, is a bijection, so `#H¹_R = #A`.  `Γ_R` twin of
`card_H1w_of_normalForm` under the `x₀ ↔ x₁` swap. -/
theorem card_H1wR_of_normalForm (t : Marking C)
    (hx1mem : ∀ d : A, x1Supported d ∈ Z1wR (A := A) t)
    (hnf : ∀ x ∈ Z1wR (A := A) t, ∃! d : A, x - x1Supported d ∈ B1wR (A := A) t) :
    Nat.card (H1wR (A := A) t) = Nat.card A := by
  have key : ∀ (a b : Z1wR (A := A) t),
      h1wMkR t a = h1wMkR t b ↔ b.val - a.val ∈ B1wR (A := A) t := by
    intro a b
    show QuotientAddGroup.mk a = QuotientAddGroup.mk b ↔ _
    rw [QuotientAddGroup.eq, AddSubgroup.mem_addSubgroupOf]
    show -a.val + b.val ∈ B1wR (A := A) t ↔ b.val - a.val ∈ B1wR (A := A) t
    rw [show -a.val + b.val = b.val - a.val from by abel]
  refine (Nat.card_eq_of_bijective (fun d => h1wMkR t ⟨x1Supported d, hx1mem d⟩) ⟨?_, ?_⟩).symm
  · -- injective
    intro c c' hcc
    rw [key] at hcc
    -- `hcc : x₁Supported c' − x₁Supported c ∈ B¹_R`
    obtain ⟨cu, -, huniq⟩ := hnf (x1Supported c) (hx1mem c)
    have e1 : c = cu := huniq c (show x1Supported c - x1Supported c ∈ B1wR (A := A) t by
      rw [sub_self]; exact (B1wR (A := A) t).zero_mem)
    have e2 : c' = cu := huniq c' (show x1Supported c - x1Supported c' ∈ B1wR (A := A) t by
      have h := (B1wR (A := A) t).neg_mem hcc; rwa [neg_sub] at h)
    exact e1.trans e2.symm
  · -- surjective
    intro h
    induction h using QuotientAddGroup.induction_on with
    | H x =>
      obtain ⟨c, hc, -⟩ := hnf x.val x.2
      exact ⟨c, (key ⟨x1Supported c, hx1mem c⟩ x).mpr hc⟩

/-- **Card clauses for a nontrivial simple module** (feeding `IsSelfDual_R`): `#H²_R = 1` and
`#Z¹_R = #A²`, from `#H¹_R = #A` (`card_H1wR_of_normalForm`), `#H⁰w = 1` (the word-free
`card_H0w_eq_one_of_nontrivial`, reused from `GQ2.DualityAssembly`), and the Euler characteristic
`card_H1w_eq_R` / rank-nullity `card_Z1w_eq_sq_mul_card_H2w_R`. -/
theorem card_H2wR_and_Z1wR_of_nontrivial_simple (t : Marking C) (ht : t.TameRel)
    (hw : t.WildRelR) (hgen : t.Generates) (hsimple : IsSimpleModTwo C A)
    (hnt : ∃ (c : C) (a : A), c • a ≠ a)
    (hx1mem : ∀ d : A, x1Supported d ∈ Z1wR (A := A) t)
    (hnf : ∀ x ∈ Z1wR (A := A) t, ∃! d : A, x - x1Supported d ∈ B1wR (A := A) t) :
    Nat.card (H2wR (A := A) t) = 1 ∧ Nat.card (Z1wR (A := A) t) = Nat.card A ^ 2 := by
  have hApos : 0 < Nat.card A := Nat.card_pos
  have hH0 : Nat.card (H0w (A := A) t) = 1 := card_H0w_eq_one_of_nontrivial t hgen hsimple hnt
  have hH1 : Nat.card (H1wR (A := A) t) = Nat.card A := card_H1wR_of_normalForm t hx1mem hnf
  have heuler := card_H1w_eq_R (A := A) t ht hw
  rw [hH1, hH0, mul_one] at heuler
  -- heuler : #A = #A * #H²_R
  have hH2 : Nat.card (H2wR (A := A) t) = 1 :=
    (Nat.eq_of_mul_eq_mul_left hApos (by rw [mul_one]; exact heuler)).symm
  refine ⟨hH2, ?_⟩
  rw [card_Z1w_eq_sq_mul_card_H2w_R, hH2, mul_one]

/-! ## `mixedB_R` descends to `H¹_R` (the degree-one pairing) -/

/-- `mixedB_R` is invariant under changing the primal argument by a coboundary (against a cocycle
dual): `B_R(x + d⁰a, y) = B_R(x, y)` since `B_R(d⁰a, y) = ⟨a, L_R(y)⟩ = 0` (`prop_5_8_left_R`,
`y` a Roe cocycle).  Uses `mixedB_R` bilinearity. -/
theorem mixedB_R_left_congr (t : Marking C) (ht : t.TameRel) (hw : t.WildRelR)
    (x x' : Fin 4 → A) (y : Fin 4 → ElemDual A) (hb : x - x' ∈ B1wR (A := A) t)
    (hy : y ∈ Z1wR (A := ElemDual A) t) :
    mixedB_R t x y = mixedB_R t x' y := by
  obtain ⟨a, ha⟩ := hb
  have hx : x = x' + d0 t a := by rw [ha]; abel
  rw [hx, mixedB_R_add_left, prop_5_8_left_R t ht hw a y]
  have hd1 : d1FunR (A := ElemDual A) t y = 0 := AddMonoidHom.mem_ker.mp hy
  simp [hd1]

/-- Dual version: `B_R(x, y + d⁰λ) = B_R(x, y)` (`prop_5_8_right_R`, `x` a Roe cocycle). -/
theorem mixedB_R_right_congr (t : Marking C) (ht : t.TameRel) (hw : t.WildRelR)
    (x : Fin 4 → A) (y y' : Fin 4 → ElemDual A) (hb : y - y' ∈ B1wR (A := ElemDual A) t)
    (hx : x ∈ Z1wR (A := A) t) :
    mixedB_R t x y = mixedB_R t x y' := by
  obtain ⟨lam, hlam⟩ := hb
  have hy : y = y' + d0 t lam := by rw [hlam]; abel
  rw [hy, mixedB_R_add_right, prop_5_8_right_R t ht hw x lam]
  have hd1 : d1FunR (A := A) t x = 0 := AddMonoidHom.mem_ker.mp hx
  simp [hd1]

/-- **Clause 3 (degree-one perfect pairing) from a normal form.**  Given that `x₁`-supported
cochains `x1Supported d` are Roe cocycles and hit every `H¹_R` class uniquely (the normal form of
⟦lem:normalforms⟧, for both `A` and `A∨`), and that the induced pairing
`d, λ ↦ B_R(x1Supported d, x1Supported λ)` is nondegenerate on both sides, `mixedB_R` descends to
a perfect pairing `H¹_R(A) × H¹_R(A∨) → 𝔽₂`.  Descent uses `mixedB_R_left_congr` /
`mixedB_R_right_congr`; nondegeneracy transports through the normal-form identification
`H¹_R ≅ A`. -/
theorem clause3_of_normalForm_R (t : Marking C) (ht : t.TameRel) (hw : t.WildRelR)
    (hx1memA : ∀ d : A, x1Supported d ∈ Z1wR (A := A) t)
    (hnfA : ∀ x ∈ Z1wR (A := A) t, ∃! d : A, x - x1Supported d ∈ B1wR (A := A) t)
    (hx1memD : ∀ lam : ElemDual A, x1Supported lam ∈ Z1wR (A := ElemDual A) t)
    (hnfD : ∀ y ∈ Z1wR (A := ElemDual A) t,
        ∃! lam : ElemDual A, y - x1Supported lam ∈ B1wR (A := ElemDual A) t)
    (hndL : ∀ d : A, d ≠ 0 →
        ∃ lam : ElemDual A, mixedB_R t (x1Supported d) (x1Supported lam) ≠ 0)
    (hndR : ∀ lam : ElemDual A, lam ≠ 0 →
        ∃ d : A, mixedB_R t (x1Supported d) (x1Supported lam) ≠ 0) :
    ∃ P : H1wR (A := A) t → H1wR (A := ElemDual A) t → ZMod 2,
      (∀ (x : Z1wR (A := A) t) (y : Z1wR (A := ElemDual A) t),
          P (h1wMkR t x) (h1wMkR t y) = mixedB_R t x.val y.val) ∧
      (∀ h, h ≠ 0 → ∃ h', P h h' ≠ 0) ∧
      (∀ h', h' ≠ 0 → ∃ h, P h h' ≠ 0) := by
  have hx1z : x1Supported (0 : A) = 0 := by ext i; fin_cases i <;> simp [x1Supported]
  have hx1zD : x1Supported (0 : ElemDual A) = 0 := by ext i; fin_cases i <;> simp [x1Supported]
  refine ⟨Quotient.lift₂ (fun (a : Z1wR (A := A) t) (b : Z1wR (A := ElemDual A) t) =>
      mixedB_R t a.val b.val) (fun a₁ b₁ a₂ b₂ h₁ h₂ => ?_), fun x y => rfl, ?_, ?_⟩
  · -- well-defined: `mixedB_R` is constant on cosets (`mixedB_R_left/right_congr`)
    have hbA : a₁.val - a₂.val ∈ B1wR (A := A) t := by
      have h := QuotientAddGroup.leftRel_apply.mp h₁
      rw [AddSubgroup.mem_addSubgroupOf] at h
      rw [show a₁.val - a₂.val = -(↑(-a₁ + a₂) : Fin 4 → A) from by push_cast; abel]
      exact (B1wR (A := A) t).neg_mem h
    have hbD : b₁.val - b₂.val ∈ B1wR (A := ElemDual A) t := by
      have h := QuotientAddGroup.leftRel_apply.mp h₂
      rw [AddSubgroup.mem_addSubgroupOf] at h
      rw [show b₁.val - b₂.val = -(↑(-b₁ + b₂) : Fin 4 → ElemDual A) from by push_cast; abel]
      exact (B1wR (A := ElemDual A) t).neg_mem h
    rw [mixedB_R_left_congr t ht hw a₁.val a₂.val b₁.val hbA b₁.2,
        mixedB_R_right_congr t ht hw a₂.val b₁.val b₂.val hbD a₂.2]
  · -- left nondegeneracy
    intro h hh
    induction h using QuotientAddGroup.induction_on with
    | H a =>
      obtain ⟨c, hc, _⟩ := hnfA a.val a.2
      have hc0 : c ≠ 0 := by
        intro hce
        rw [hce, hx1z, sub_zero] at hc
        exact hh ((QuotientAddGroup.eq_zero_iff a).mpr (AddSubgroup.mem_addSubgroupOf.mpr hc))
      obtain ⟨lam, hlam⟩ := hndL c hc0
      refine ⟨QuotientAddGroup.mk ⟨x1Supported lam, hx1memD lam⟩, ?_⟩
      show mixedB_R t a.val (x1Supported lam) ≠ 0
      rwa [mixedB_R_left_congr t ht hw a.val (x1Supported c) (x1Supported lam) hc (hx1memD lam)]
  · -- right nondegeneracy
    intro h hh
    induction h using QuotientAddGroup.induction_on with
    | H b =>
      obtain ⟨lam, hlam, _⟩ := hnfD b.val b.2
      have hlam0 : lam ≠ 0 := by
        intro hle
        rw [hle, hx1zD, sub_zero] at hlam
        exact hh ((QuotientAddGroup.eq_zero_iff b).mpr (AddSubgroup.mem_addSubgroupOf.mpr hlam))
      obtain ⟨c, hc⟩ := hndR lam hlam0
      refine ⟨QuotientAddGroup.mk ⟨x1Supported c, hx1memA c⟩, ?_⟩
      show mixedB_R t (x1Supported c) b.val ≠ 0
      rwa [mixedB_R_right_congr t ht hw (x1Supported c) b.val (x1Supported lam) hlam (hx1memA c)]

/-! ## Split simple case: `Z¹_R`/`B¹_R` shapes, normal form, `x₁`-support

These are phrased against the split *shapes* (rather than `lemma_5_13_split_R` directly) so they
apply equally to `A` and its contragredient dual `A∨`: the dual is split with trivial wild action
whenever `A` is, without needing "the dual of a simple module is simple". -/

/-- The split `Z¹_R`/`B¹_R` shapes from a *trivial wild action* (`hx0`, `hx1`) rather than from
simplicity — the body of `lemma_5_13_split_R` with `wild_acts_trivially` factored out as
hypotheses, so it is usable on `A∨` (where wild-triviality comes from the contragredient of
`A`'s).  Unlike `Γ_A`'s `split_shapes_of_wild` there is **no `hU`**: the Roe wild row
`liftMarking_wildValueR_u` carries no `σ₂`-tameness dependency. -/
theorem split_shapes_of_wild_R (t : Marking C) (ht : t.TameRel)
    (hV₂ : ∀ v : A, v + v = 0) (hx0 : ∀ v : A, t.x₀ • v = v) (hx1 : ∀ v : A, t.x₁ • v = v)
    (htau : ∀ v : A, t.τ • v = v) (hVS : ∀ v : A, t.σ • v = v → v = 0) :
    (∀ x : Fin 4 → A, x ∈ Z1wR (A := A) t ↔ x 1 = 0 ∧ x 2 = 0) ∧
    (∀ y : Fin 4 → A, y ∈ B1wR (A := A) t ↔ ∃ v : A, y = ![t.σ • v - v, 0, 0, 0]) := by
  refine ⟨fun x => ?_, fun y => b1wR_split_shape t htau hx0 hx1 y⟩
  rw [mem_Z1wR_iff t x, Prod.ext_iff]
  rw [d1FunR_fst t x, d1Fun_tame_split t ht htau hV₂ x, d1FunR_snd t x,
    liftMarking_wildValueR_u t x hV₂ hx0 hx1 htau]
  simp only [Prod.fst_zero, Prod.snd_zero]
  constructor
  · rintro ⟨h1, h2⟩
    have hx1z : x 1 = 0 := by rwa [inv_smul_eq_iff, smul_zero] at h1
    rw [hx1z, zero_add] at h2
    have h3 : t.σ⁻¹ • x 2 = x 2 :=
      (add_eq_zero_iff_neg_eq.mp h2).symm.trans (neg_eq_of_add_eq_zero_left (hV₂ (x 2)))
    exact ⟨hx1z, hVS _ (inv_smul_eq_iff.mp h3).symm⟩
  · rintro ⟨h1, h3⟩
    simp [h1, h3]

/-- The `x₁`-supported cochains are Roe cocycles, straight from the split `Z¹_R` shape. -/
theorem x1mem_of_Z1wRShape (t : Marking C)
    (hZ : ∀ x : Fin 4 → A, x ∈ Z1wR (A := A) t ↔ x 1 = 0 ∧ x 2 = 0) :
    ∀ d : A, x1Supported d ∈ Z1wR (A := A) t := fun d => by
  simp [hZ, x1Supported]

/-- **Split normal form**: from the `Z¹_R`/`B¹_R` shapes and surjectivity of `σ − 1` (from
`V^S = 0`, `hVS`), every degree-one class has a unique `x₁`-supported representative. -/
theorem normalForm_of_shapes_R (t : Marking C)
    (hZ : ∀ x : Fin 4 → A, x ∈ Z1wR (A := A) t ↔ x 1 = 0 ∧ x 2 = 0)
    (hB : ∀ y : Fin 4 → A, y ∈ B1wR (A := A) t ↔ ∃ v : A, y = ![t.σ • v - v, 0, 0, 0])
    (hVS : ∀ v : A, t.σ • v = v → v = 0) :
    ∀ x ∈ Z1wR (A := A) t, ∃! d : A, x - x1Supported d ∈ B1wR (A := A) t := by
  have hsurj : Function.Surjective (fun v : A => t.σ • v - v) :=
    surjective_smul_sub_of_fixedPointFree hVS
  intro x hx
  rw [hZ] at hx
  obtain ⟨hx1, hx2⟩ := hx
  refine ⟨x 3, ?_, ?_⟩
  · show x - x1Supported (x 3) ∈ B1wR (A := A) t
    rw [hB]
    obtain ⟨v, hv⟩ := hsurj (x 0)
    exact ⟨v, by funext i; fin_cases i <;> simp [x1Supported, Pi.sub_apply, hx1, hx2, hv]⟩
  · intro d hd
    rw [hB] at hd
    obtain ⟨w, hw'⟩ := hd
    have h3 := congrFun hw' 3
    have hdw : (0 : A) = x 3 - d := by simpa [x1Supported, Pi.sub_apply] using h3.symm
    exact (sub_eq_zero.mp hdw.symm).symm

/-! ## Split simple case: `IsSelfDual_R` -/

/-- **⟦prop:duality⟧, split simple case.**  A nontrivial simple module on which `τ` acts trivially
(`htau`) and `σ` acts nontrivially (`hσ`) is self-dual for the Roe complex.  The fixed-point
freeness `hVS` comes from the tame representation-theory proof (`fixedPoints_sigma_eq_zero`); the
contragredient dual `A∨` inherits split + trivial-wild action from `A` (via
`elemDual_smul_trivial_of`), giving both normal forms; the cards close clauses 1–2 and
`clause3_of_normalForm_R` (with the split pairing `(d,λ) ↦ λ(d)`, `mixedB_R_pairing_split` —
whose `hU` is `sigma2_smul_trivial`, needed only here, not in the shapes) closes clause 3. -/
theorem selfDual_of_split_R (t : Marking C) (ht : t.TameRel) (hw : t.WildRelR)
    (hgen : t.Generates) (hV₂ : ∀ v : A, v + v = 0) (hsimple : IsSimpleModTwo C A)
    (hcore : t.Pro2Core) (htau : ∀ v : A, t.τ • v = v) (hσ : ∃ v : A, t.σ • v ≠ v) :
    IsSelfDual_R t A := by
  obtain ⟨v₀, hv₀⟩ := hσ
  have hnt : ∃ (c : C) (a : A), c • a ≠ a := ⟨t.σ, v₀, hv₀⟩
  -- `A`-side hypotheses (the tame representation-theory proof) and the split shapes / normal form
  have hU : ∀ v : A, t.sigma2 • v = v := sigma2_smul_trivial t hgen hV₂ hsimple hcore htau
  have hVS : ∀ v : A, t.σ • v = v → v = 0 :=
    fixedPoints_sigma_eq_zero t hgen hV₂ hsimple hcore htau ⟨v₀, hv₀⟩
  obtain ⟨hx0, hx1⟩ := wild_acts_trivially t hV₂ hsimple hcore
  have hsurjA : Function.Surjective (fun v : A => t.σ • v - v) :=
    surjective_smul_sub_of_fixedPointFree hVS
  obtain ⟨hZA, hBA⟩ := split_shapes_of_wild_R t ht hV₂ hx0 hx1 htau hVS
  have hnfA := normalForm_of_shapes_R t hZA hBA hVS
  have hx1A := x1mem_of_Z1wRShape t hZA
  -- The contragredient dual is split with trivial wild action (transfer of `A`'s triviality)
  have hV₂D : ∀ l : ElemDual A, l + l = 0 := fun l => l.add_self_eq_zero
  have hx0D := elemDual_smul_trivial_of (A := A) t.x₀ hx0
  have hx1D := elemDual_smul_trivial_of (A := A) t.x₁ hx1
  have htauD := elemDual_smul_trivial_of (A := A) t.τ htau
  have hVSD : ∀ l : ElemDual A, t.σ • l = l → l = 0 := by
    intro l hl
    have hlσ : ∀ x : A, l (t.σ • x) = l x := fun x => by
      have h := ElemDual.smul_apply t.σ l (t.σ • x)
      rwa [inv_smul_smul, hl] at h
    ext a
    obtain ⟨b, hb⟩ := hsurjA a
    have hb' : t.σ • b - b = a := hb
    rw [ElemDual.zero_apply, ← hb', map_sub, hlσ b, sub_self]
  obtain ⟨hZD, hBD⟩ := split_shapes_of_wild_R (A := ElemDual A) t ht hV₂D hx0D hx1D htauD hVSD
  have hnfD := normalForm_of_shapes_R (A := ElemDual A) t hZD hBD hVSD
  have hx1D' := x1mem_of_Z1wRShape (A := ElemDual A) t hZD
  -- Cards (clauses 1–2) and the perfect pairing (clause 3)
  obtain ⟨hcard2, hcardZ⟩ :=
    card_H2wR_and_Z1wR_of_nontrivial_simple t ht hw hgen hsimple hnt hx1A hnfA
  have hfix1 := card_fixedPts_elemDual_eq_one_of_nontrivial (A := A) hsimple hnt
  refine ⟨by rw [hcard2, hfix1], by rw [hcardZ, hfix1, mul_one],
    clause3_of_normalForm_R t ht hw hx1A hnfA hx1D' hnfD ?_ ?_⟩
  · intro c hc
    obtain ⟨lam, hlam⟩ := elemDual_separates hV₂ hc
    exact ⟨lam, by
      rw [mixedB_R_pairing_split t hV₂ hx0 hx1 htau hU c lam]; exact hlam⟩
  · intro lam hlam
    obtain ⟨c, hc⟩ := DFunLike.ne_iff.mp hlam
    exact ⟨c, by
      rw [mixedB_R_pairing_split t hV₂ hx0 hx1 htau hU c lam]; simpa using hc⟩

/-- **Trivial-action case.**  If all four generators act trivially then (by `hgen`) every element
of `C` does, and the module is self-dual for the Roe complex by R25's `trivialSelfDual_R`.  This
is the split sub-case where `σ` also acts trivially. -/
theorem selfDual_of_trivial_action_R (t : Marking C) (ht : t.TameRel) (hw : t.WildRelR)
    (hgen : t.Generates) (hV₂ : ∀ v : A, v + v = 0)
    (hσ : ∀ v : A, t.σ • v = v) (htau : ∀ v : A, t.τ • v = v)
    (hx0 : ∀ v : A, t.x₀ • v = v) (hx1 : ∀ v : A, t.x₁ • v = v) :
    IsSelfDual_R t A := by
  have htriv : ∀ (c : C) (v : A), c • v = v := by
    have hle : Subgroup.closure {t.σ, t.τ, t.x₀, t.x₁} ≤
        ({ carrier := {g | ∀ v : A, g • v = v}
           one_mem' := fun v => one_smul C v
           mul_mem' := fun {a b} ha hb v => by rw [mul_smul, hb v, ha v]
           inv_mem' := fun {a} ha v => by
             rw [inv_smul_eq_iff]; exact (ha v).symm } : Subgroup C) := by
      rw [Subgroup.closure_le]
      intro g hg
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
      rcases hg with rfl | rfl | rfl | rfl
      · exact hσ
      · exact htau
      · exact hx0
      · exact hx1
    rw [hgen] at hle
    exact fun c v => hle (Subgroup.mem_top c) v
  exact trivialSelfDual_R t ht hw htriv hV₂

/-! ## Ramified simple case -/

/-- In the ramified case the `x₁`-supported cochains are Roe cocycles: the shared tame row
(`d1Fun_tame`) involves only coordinates 0 and 1, the Roe wild row is `S⁻¹x₂`
(`liftMarking_wildValueR_u_ramified`), and all three coordinates vanish on `x1Supported d`. -/
theorem x1Supported_mem_Z1wR_ramified (t : Marking C) (ht : t.TameRel)
    (hV₂ : ∀ v : A, v + v = 0)
    (hx0 : ∀ v : A, t.x₀ • v = v) (hx1 : ∀ v : A, t.x₁ • v = v)
    (htau : ∀ v : A, t.τ • v = v → v = 0) (hTodd : ∀ v : A, powOmega2 t.τ • v = v) :
    ∀ d : A, x1Supported d ∈ Z1wR (A := A) t := by
  intro d
  rw [mem_Z1wR_iff t (x1Supported d), Prod.ext_iff]
  simp only [Prod.fst_zero, Prod.snd_zero]
  refine ⟨?_, ?_⟩
  · rw [d1FunR_fst t (x1Supported d), d1Fun_tame t ht (x1Supported d)]
    simp [x1Supported]
  · rw [d1FunR_snd t (x1Supported d),
      liftMarking_wildValueR_u_ramified t (x1Supported d) hV₂ hx0 hx1 htau hTodd]
    simp [x1Supported]

/-- **⟦prop:duality⟧, ramified simple case.**  A simple module with `V^T = 0` is self-dual for
the Roe complex.  `hTodd` (τ odd-order) is derived (`tau_powOmega2_smul_trivial`); the dual `A∨`
inherits wild-triviality and `hTodd` (contragredient) and τ-fixed-point-freeness (`(τ⁻¹−1)`
surjective); the pairing `λ((1+U+U⁻¹)d)` (`mixedB_R_pairing_ramified`, ⟦eq:pairingoperator⟧) is
perfect because the operator `1+U+U⁻¹` is unipotent, hence bijective
(`pairingR_operator_injective`) — no σ-tameness `hU` anywhere in this branch. -/
theorem selfDual_of_ramified_R (t : Marking C) (ht : t.TameRel) (hw : t.WildRelR)
    (hgen : t.Generates) (hV₂ : ∀ v : A, v + v = 0) (hsimple : IsSimpleModTwo C A)
    (hcore : t.Pro2Core) (htau : ∀ v : A, t.τ • v = v → v = 0) :
    IsSelfDual_R t A := by
  obtain ⟨hx0, hx1⟩ := wild_acts_trivially t hV₂ hsimple hcore
  have hTodd : ∀ v : A, powOmega2 t.τ • v = v :=
    tau_powOmega2_smul_trivial t ht hgen hV₂ hsimple hcore
  -- the action is nontrivial: `τ` is fixed-point-free on a nontrivial module
  haveI : Nontrivial A := hsimple.1
  obtain ⟨a₀, ha₀⟩ := exists_ne (0 : A)
  have hnt : ∃ (c : C) (a : A), c • a ≠ a := ⟨t.τ, a₀, fun h => ha₀ (htau a₀ h)⟩
  -- `A`-side normal form
  have hx1A := x1Supported_mem_Z1wR_ramified t ht hV₂ hx0 hx1 htau hTodd
  have hnfA := lemma_5_13_ramified_R t ht hw hV₂ hx0 hx1 htau hTodd
  -- the pairing operator `1 + U + U⁻¹` is bijective (unipotent in char 2)
  have hop := pairingR_operator_injective (V := A) t hV₂
  have hopsurj := Finite.injective_iff_surjective.mp hop
  -- dual-side hypotheses
  have hV₂D : ∀ l : ElemDual A, l + l = 0 := fun l => l.add_self_eq_zero
  have hx0D := elemDual_smul_trivial_of (A := A) t.x₀ hx0
  have hx1D := elemDual_smul_trivial_of (A := A) t.x₁ hx1
  have hToddD := elemDual_smul_trivial_of (A := A) (powOmega2 t.τ) hTodd
  have hτsurj : Function.Surjective (fun v : A => t.τ⁻¹ • v - v) :=
    surjective_smul_sub_of_fixedPointFree fun v hv => htau v (inv_smul_eq_iff.mp hv).symm
  have htauD : ∀ l : ElemDual A, t.τ • l = l → l = 0 := by
    intro l hl
    have hlτ : ∀ x : A, l (t.τ⁻¹ • x) = l x := fun x => by
      have h := congrArg (fun m : ElemDual A => m x) hl
      rwa [ElemDual.smul_apply] at h
    ext a
    obtain ⟨b, hb⟩ := hτsurj a
    have hb' : t.τ⁻¹ • b - b = a := hb
    rw [ElemDual.zero_apply, ← hb', map_sub, hlτ b, sub_self]
  have hx1D' := x1Supported_mem_Z1wR_ramified (A := ElemDual A) t ht hV₂D hx0D hx1D htauD
    hToddD
  have hnfD := lemma_5_13_ramified_R (V := ElemDual A) t ht hw hV₂D hx0D hx1D htauD hToddD
  -- cards (clauses 1–2) and the perfect pairing (clause 3)
  obtain ⟨hcard2, hcardZ⟩ :=
    card_H2wR_and_Z1wR_of_nontrivial_simple t ht hw hgen hsimple hnt hx1A hnfA
  have hfix1 := card_fixedPts_elemDual_eq_one_of_nontrivial (A := A) hsimple hnt
  refine ⟨by rw [hcard2, hfix1], by rw [hcardZ, hfix1, mul_one],
    clause3_of_normalForm_R t ht hw hx1A hnfA hx1D' hnfD ?_ ?_⟩
  · intro c hc
    have hne : c + t.sigma2 • c + t.sigma2⁻¹ • c ≠ 0 := by
      intro h0
      exact hc (hop (show (fun v : A => v + t.sigma2 • v + t.sigma2⁻¹ • v) c
        = (fun v : A => v + t.sigma2 • v + t.sigma2⁻¹ • v) 0 from by
          simp only [smul_zero, add_zero, h0]))
    obtain ⟨lam, hlam⟩ := elemDual_separates hV₂ hne
    refine ⟨lam, ?_⟩
    rwa [mixedB_R_pairing_ramified t hV₂ hx0 hx1 htau hTodd c lam]
  · intro lam hlam
    obtain ⟨w, hw'⟩ := DFunLike.ne_iff.mp hlam
    obtain ⟨c, hc⟩ := hopsurj w
    refine ⟨c, ?_⟩
    rw [mixedB_R_pairing_ramified t hV₂ hx0 hx1 htau hTodd c lam,
      show c + t.sigma2 • c + t.sigma2⁻¹ • c = w from hc]
    simpa using hw'

/-- **Split case of a simple module (complete).**  When `τ` acts trivially, the simple module is
self-dual for the Roe complex — whether `σ` acts nontrivially (`selfDual_of_split_R`) or
trivially (`selfDual_of_trivial_action_R`).  This closes the entire `V^T = V` branch of the
`tau_split_or_ramified` dichotomy. -/
theorem selfDual_of_split_case_R (t : Marking C) (ht : t.TameRel) (hw : t.WildRelR)
    (hgen : t.Generates) (hV₂ : ∀ v : A, v + v = 0) (hsimple : IsSimpleModTwo C A)
    (hcore : t.Pro2Core) (htau : ∀ v : A, t.τ • v = v) :
    IsSelfDual_R t A := by
  by_cases hσ : ∃ v : A, t.σ • v ≠ v
  · exact selfDual_of_split_R t ht hw hgen hV₂ hsimple hcore htau hσ
  · push Not at hσ
    obtain ⟨hx0, hx1⟩ := wild_acts_trivially t hV₂ hsimple hcore
    exact selfDual_of_trivial_action_R t ht hw hgen hV₂ hσ htau hx0 hx1

/-- **The simple case of `prop_5_15_R`, unconditional** (⟦prop:duality⟧, "the cone of the chain
map is acyclic on all simple modules"): every finite simple char-2 module at an admissible-style
marking is self-dual for the Roe complex.  Dispatches on the word-free `tau_split_or_ramified`
dichotomy (reused from `GQ2.DualityAssembly`) — `selfDual_of_split_case_R` for `V^T = V`,
`selfDual_of_ramified_R` for `V^T = 0`.  This is exactly the `hsimp` input the dévissage
induction (`prop_5_15_of_simple_R`) consumes. -/
theorem selfDual_of_simple_R (t : Marking C) (ht : t.TameRel) (hw : t.WildRelR)
    (hgen : t.Generates) (hcore : t.Pro2Core) (hV₂ : ∀ v : A, v + v = 0)
    (hsimple : IsSimpleModTwo C A) :
    IsSelfDual_R t A := by
  rcases tau_split_or_ramified t ht hgen hsimple hcore hV₂ with htau | htau
  · exact selfDual_of_split_case_R t ht hw hgen hV₂ hsimple hcore htau
  · exact selfDual_of_ramified_R t ht hw hgen hV₂ hsimple hcore htau

/-- **⟦prop:duality⟧ (Candidate deformation duality), word half:** the Roe word complex is
self-dual for every finite elementary module — packaged: the display-(56) numerics hold on the
`r_R` complex and the descended `B_R`-pairing is perfect.

The composition: the dévissage strong induction `prop_5_15_of_simple_R`
(`GQ2/Roe/DevissageInduction.lean`, via `lemma_5_11_R` along `0 → W → A → A/W → 0` for a proper
`C`-stable `W`) reduces to the simple case, which `selfDual_of_simple_R` closes by the
`tau_split_or_ramified` dichotomy — split (`split_shapes_of_wild_R` + the tame
representation-theory providers) or ramified (`lemma_5_13_ramified_R` + `hTodd` derived + the
unipotent pairing operator).  `Γ_R` twin of `GQ2.FoxH.prop_5_15`. -/
theorem prop_5_15_R (t : Marking C) (ht : t.TameRel) (hw : t.WildRelR) (hgen : t.Generates)
    (hA₂ : ∀ a : A, a + a = 0) (hcore : t.Pro2Core) :
    IsSelfDual_R t A :=
  prop_5_15_of_simple_R t ht hw hgen
    (fun _ _ _ _ hB₂ hBsimple => selfDual_of_simple_R t ht hw hgen hcore hB₂ hBsimple) hA₂

end Assembly

/-! ## §5.17 numerics on the `r_R` spine

The local half `prop_5_16` (`GQ2/LocalLiftingDuality.lean`) is **word-generic** — its statement
and proof never mention the marking word — so it is reused verbatim (campaign convention: never
clone word-free infrastructure).  The corollary is therefore a thin splice. -/

section Cor517

open GQ2.ContCoh GQ2.LocalLiftingDuality

/-- **Corollary 5.17, numerics half, on the `r_R` spine** (⟦prop:duality⟧, "Comparison with the
local complex then uses local Tate duality as in [RT Prop. 5.16 and Cor. 5.17]"): the
obstruction-space and unobstructed-lift-multiplicity cardinalities agree between the Roe word
complex and the local cochain complex of `G_ℚ₂`.  `Γ_R` twin of `cor_5_17_card`: the word side is
`prop_5_15_R` (clauses 1–2 of `IsSelfDual_R`), the local side is the **word-generic** `prop_5_16`
reused verbatim (this is where axioms B6/B7 enter, exactly as for `Γ_A`). -/
theorem cor_5_17_card_R {C : Type*} [Group C] [TopologicalSpace C] [DiscreteTopology C]
    [Finite C]
    (t : Marking C) (ht : t.TameRel) (hw : t.WildRelR) (hgen : t.Generates)
    (hcore : t.Pro2Core)
    (ρ : ContinuousMonoidHom AbsGalQ2 C) (hρ : Function.Surjective ρ)
    {A : Type} [AddCommGroup A] [TopologicalSpace A] [DiscreteTopology A] [Finite A]
    [DistribMulAction C A]
    [DistribMulAction AbsGalQ2 A] [ContinuousSMul AbsGalQ2 A]
    (hcomp : ∀ (γ : AbsGalQ2) (a : A), γ • a = ρ γ • a)
    (hA₂ : ∀ a : A, a + a = 0)
    [TopologicalSpace (ElemDual A)] [DiscreteTopology (ElemDual A)]
    [DistribMulAction AbsGalQ2 (ElemDual A)] [ContinuousSMul AbsGalQ2 (ElemDual A)]
    (hcompD : ∀ (γ : AbsGalQ2) (lam : ElemDual A), γ • lam = ρ γ • lam)
    [TopologicalSpace (ZMod 2)] [DiscreteTopology (ZMod 2)]
    [DistribMulAction AbsGalQ2 (ZMod 2)] [ContinuousSMul AbsGalQ2 (ZMod 2)]
    (htriv : ∀ (γ : AbsGalQ2) (m : ZMod 2), γ • m = m)
    (hpair : ∀ (γ : AbsGalQ2) (a : A) (lam : ElemDual A),
      dualEval A (γ • a) (γ • lam) = γ • dualEval A a lam) :
    Nat.card (Z1wR (A := A) t) = Nat.card (ContCoh.Z1 AbsGalQ2 A) ∧
    Nat.card (H2wR (A := A) t) = Nat.card (ContCoh.H2 AbsGalQ2 A) := by
  obtain ⟨hc2, hc1, -⟩ := prop_5_15_R t ht hw hgen (A := A) hA₂ hcore
  obtain ⟨hl2, hl1, -⟩ := prop_5_16 ρ hρ (A := A) hcomp hA₂ hcompD htriv hpair
  exact ⟨hc1.trans hl1.symm, hc2.trans hl2.symm⟩

end Cor517

end FoxH

end GQ2

/-! ### Paper-tag ledger (Roe note `paper/roe-presentation-verification.tex`; hand-maintained)

  * Proposition (Candidate deformation duality) = ⟦prop:duality⟧ — `selfDual_of_simple_R` (the
    simple case: ⟦lem:normalforms⟧ + ⟦prop:hessian⟧/⟦eq:pairingoperator⟧ + R25's ⟦lem:trivial⟧
    base) and `prop_5_15_R` (the full assembly through the dévissage induction).  The local
    comparison sentence of its proof ("Comparison with the local complex then uses local Tate
    duality as in [RT Prop. 5.16 and Cor. 5.17]") is `cor_5_17_card_R`, splicing the
    word-generic `prop_5_16` (reused verbatim from `GQ2/LocalLiftingDuality.lean`, axioms B6/B7)
    against `prop_5_15_R`.
-/
