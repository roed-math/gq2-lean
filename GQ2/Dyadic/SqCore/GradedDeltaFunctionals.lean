/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Fable 5
-/
import GQ2.Dyadic.SqCore.GradedClassFourCompose
import GQ2.Dyadic.SqCore.GradedLimit
import GQ2.Roe.CrossedDerivation
import GQ2.PropOneOne

/-!
# W74-FUNC: the graded delta functionals (Labute's Lemma 4 for the sq core)

Labute's Lemma 4 (CJM 19 (1967), p. 125) controls the graded layers of a Demushkin
one-relator group by **crossed homomorphisms** `D` into the chi-twisted module: `D`
respects the lower 2-central filtration (`D(F_i) ⊆ 2^i I`), induces linear functionals
`Delta` on the layers, detects the Frobenius towers (`Delta_i(pi^{j-1} xi_k) = pi^j
delta_ik`, `k` not the excluded letter), and kills every dressed relator (`Delta ∘ delta
= 0`).  This file commits that mechanism for the campaign's core `D_sq h`, directly on
the committed objects.  See `docs/dyadic/w74-func-note.md` for the full identification
audit (T0), including why the twist is load-bearing and cannot be dropped at the layer
bit.

## Contents

* **§1 The lift target.**  The crossed-derivation lift group `WordLift ℤ₂ ℤ₂ˣ` of
  `GQ2/FoxHeisenberg/Basic.lean` (whose multiplication *is* the crossed rule
  `D(xy) = Dx + χ(x)Dy`) is made a pro-2 topological group: product topology,
  compactness, and `gDelta_isProP : IsProP 2 (WordLift ℤ₂ ℤ₂ˣ)`.

  ⚠ **Instance scope**: `GQ2/WordCohBridge.lean` globally installs the *discrete*
  topology on every `WordLift A C`, and that file is in this module's import closure.
  The instances here are therefore `local instance` (priority 2000) *inside this file
  only*, exported as plain defs (`gDeltaTop`, ...).  Exported constants bake the
  correct instances into their types, so consumers never re-resolve them; a consumer
  stating *new* topological facts about the lift group should re-attach
  `attribute [local instance 2000] gDeltaTop gDeltaTopGroup gDeltaCompact gDeltaT2
  gDeltaTotDisc` locally, and must not do so in a file that also elaborates against
  the discrete instances.

* **§2 The functionals.**  For every row `c : Fin (sqRank h) → ℤ₂`,
  ⭐⭐⭐ `gDeltaHom h c : ContinuousMonoidHom (DSq h) (WordLift ℤ₂ ℤ₂ˣ)` with generator
  values `⟨c i, χ-mark i⟩` — the continuous crossed homomorphism `gDelta h c` with
  `gDelta (sqGen i) = c i`, twisted by exactly `χ_sq` (`gDeltaHom_g`).  The relator
  dies by the committed datum theorem (`isLabuteOrientationDatum_of_root`, i.e.
  Labute's Théorème 4 computation, plus the handle lemma `handleWord_wordLift_one`);
  this is the quotient-side existence that Labute gets from freeness, and it holds at
  **every** row — strictly more than the corank-1 lattice of untwisted rows (the
  committed `nuSq`/`nuLam`/`nu'` markings).  Crossed product/inverse/power/commutator
  rules follow (`gDelta_mul`, `gDelta_inv`, `gDelta_pow`, `gDelta_commP`,
  `gDelta_commutatorElement`).

* **§3 The filtration** (Labute Lemma 4(1)).  ⭐⭐ `gDelta_dvd_of_mem_twoCentral`:
  `x ∈ λ_{k+1}` forces `2^k ∣ gDelta h c x`; with rows in `2ℤ₂`
  (`gDelta_two_dvd`) this is Labute's `D(F_i) ⊆ 2^i I` on the nose.  Consequently
  `gDelta` reads each layer `λ_{k+1}/λ_{k+2}` through the single bit
  `gDelta mod 2^{k+1}`, and the reading is lift-independent
  (`gDelta_dvd_of_levelMk_eq`).

* **§4 The towers** (Labute Lemma 4(3)).  `gDelta h c (x ^ 2^m) = N_{2^m}(χ(x)) ·
  gDelta h c x` with `N` the committed `normSum`; at `σ` and `x₀` the geometric sum is
  `2^m · unit` (⭐ `gDelta_sigma_tower`, `gDelta_x0_tower`; the mod-16 congruences `S ≡
  13`, `X ≡ 5` give `v₂(S−1) = v₂(X−1) = 2`), at a handle letter it is exactly `2^m`
  (`gDelta_handle_tower`), and the tower nonvanishing corollaries
  ⭐⭐ `gDelta_sigma_tower_notMem`/`gDelta_x0_tower_notMem`/`gDelta_handle_tower_notMem`
  place `gen^{2^m}` outside `λ_{m+2}`: the towers are nontrivial layer classes at
  every level, and the functionals separate them.  The excluded letter is `x₁`
  (`χ(x₁) = Y ≡ 3 mod 4`): ⭐⭐ `gDelta_x1_tower_dvd` gives `2^{m+2} ∣ gDelta (x₁^{2^m})`
  for `m ≥ 1` and every row — **no** functional sees the `x₁` tower.  This is
  Labute's `k ≠ 2` side condition, and it is the functional-side face of the graded
  campaign's finding that the `x₁`-slot square knob is the delicate direction.

* **§5 Vanishing on the defects** (Labute Lemma 4(2): a dressed relator is a relator).
  The chi-triviality inventory (`gDelta_chiSq_sqEichU/V`, `gDelta_chiSq_bridgeDress`,
  from the committed `chiSq_sqPivot`), then the master kill
  ⭐⭐⭐ `gDelta_relWord_of_chiFrame`: any frame with the standard chi-values has
  `gDeltaHom h c (sqRelWord m) = 1` — the level-generic defect shape of
  `SqClassClearingSupply`, killed at every class at once.  Instances: the wave-68
  leftover lift dies exactly (⭐⭐⭐ `gDelta_leftover_lift`), every lift of
  `cfourIdLeftover` and of `cfourEichDefect` satisfies `2^3 ∣ gDelta`
  (`gDelta_dvd_of_levelMk_eq_leftover`, `gDelta_dvd_of_levelMk_eq_eichDefect`), and
  the supply-shaped statement is packaged as the interface Prop
  ⭐⭐⭐ `GDeltaDefectVanishing h`, proved outright (`gDeltaDefectVanishing_holds`).

* **§6 The core defect, sharply.**  `cfourDefCore` is *not* a pure relator shape and
  is *not* exactly killed: on the canonical lift,
  ⭐⭐ `gDelta_coreLift_eq` evaluates it in closed form,
  `(X⁻¹ − S⁻¹) · gDelta h c (bridgeDress nu' j)`, and `v₂(S − X) = 3` exactly
  (`S − X ≡ 8 mod 16`, `gDelta_Sval_sub_rootX`), so every lift satisfies
  `2^3 ∣ gDelta` (`gDelta_dvd_of_levelMk_eq_defCore`): the layer-three reading of the
  core defect vanishes for every row, i.e. **the class-four residual carries no
  component along any functional-protected tower**.  For rows in `2ℤ₂` the bound
  sharpens to `2^4` (`gDelta_coreLift_dvd_of_even`), the full class-four precision.

* **§7 The honesty artifacts.**  (i) The untwisted reading
  `f (sqRelWord m) = (f (m 1)^4)⁻¹ (f (m 2))^2` for every character `f`
  (`gDelta_row_reading`): combined with the note §1.3 computation it shows untwisted
  rows cannot kill the leftover, so the twist in §2 is not removable.  (ii) The
  torsion gap: the supply's row clauses force only `χ_sq(a)² = 1`
  (`gDelta_chiSq_sq_of_nuLam`), i.e. `χ_sq(a) = ±1`
  (`gDelta_chiSq_of_nuLam`); the `-1` branch evades the §5 kill and is the exact gap
  between `GDeltaDefectVanishing` and the supply's full dressing space.  Recorded for
  the W75 assembly.

Lane W74-FUNC.  New file; no edits to existing files.  Prefix `gDelta`.
-/

open Multiplicative

namespace GQ2

open Roe Roe.Labute FoxH

namespace Dyadic

namespace SqCore

open MarkedCore

/- The mathlib element bracket is opened deliberately: §3 consumes
`Subgroup.commutator_le`, whose element form is `⁅v, g⁆ = v g v⁻¹ g⁻¹`.  This file
uses BOTH brackets and never identifies them: `commP a b = a⁻¹b⁻¹ab` has the rule
`gDelta_commP`, `⁅a, b⁆` has the rule `gDelta_commutatorElement`, and the relation
`commP a b = ⁅a⁻¹, b⁻¹⁆` is used exactly once, inside the filtration proof. -/
open scoped commutatorElement

/-! ## §1 The lift target: `WordLift ℤ₂ ℤ₂ˣ` as a pro-2 topological group -/

/-- The product topology on the crossed-derivation lift group, induced along the
committed `WordLift.equivProd`.  A **file-local** instance (priority 2000); see the
module docstring's instance-scope warning about `GQ2/WordCohBridge.lean`. -/
@[reducible] noncomputable def gDeltaTop : TopologicalSpace (WordLift ℤ_[2] ℤ_[2]ˣ) :=
  TopologicalSpace.induced (WordLift.equivProd (A := ℤ_[2]) (C := ℤ_[2]ˣ)) inferInstance

attribute [local instance 2000] gDeltaTop

theorem gDelta_continuous_equivProd :
    Continuous (WordLift.equivProd (A := ℤ_[2]) (C := ℤ_[2]ˣ)) :=
  continuous_induced_dom

/-- The derivation component is continuous. -/
theorem gDelta_continuous_u :
    Continuous (WordLift.u : WordLift ℤ_[2] ℤ_[2]ˣ → ℤ_[2]) :=
  continuous_fst.comp gDelta_continuous_equivProd

/-- The character component is continuous. -/
theorem gDelta_continuous_g :
    Continuous (WordLift.g : WordLift ℤ_[2] ℤ_[2]ˣ → ℤ_[2]ˣ) :=
  continuous_snd.comp gDelta_continuous_equivProd

theorem gDelta_continuous_equivProd_symm :
    Continuous (WordLift.equivProd (A := ℤ_[2]) (C := ℤ_[2]ˣ)).symm :=
  continuous_induced_rng.mpr (continuous_id.congr fun x =>
    ((WordLift.equivProd (A := ℤ_[2]) (C := ℤ_[2]ˣ)).apply_symm_apply x).symm)

/-- `WordLift ℤ₂ ℤ₂ˣ ≃ₜ ℤ₂ × ℤ₂ˣ`. -/
noncomputable def gDeltaHomeo : WordLift ℤ_[2] ℤ_[2]ˣ ≃ₜ ℤ_[2] × ℤ_[2]ˣ :=
  { WordLift.equivProd with
    continuous_toFun := gDelta_continuous_equivProd
    continuous_invFun := gDelta_continuous_equivProd_symm }

/-- The lift group is a topological group.  File-local instance; see §1's warning. -/
theorem gDeltaTopGroup : IsTopologicalGroup (WordLift ℤ_[2] ℤ_[2]ˣ) where
  continuous_mul := by
    refine continuous_induced_rng.mpr ?_
    have hcont : Continuous fun p : WordLift ℤ_[2] ℤ_[2]ˣ × WordLift ℤ_[2] ℤ_[2]ˣ =>
        ((p.1.u + (p.1.g : ℤ_[2]) * p.2.u, p.1.g * p.2.g) : ℤ_[2] × ℤ_[2]ˣ) :=
      ((gDelta_continuous_u.comp continuous_fst).add
        ((Units.continuous_val.comp (gDelta_continuous_g.comp continuous_fst)).mul
          (gDelta_continuous_u.comp continuous_snd))).prodMk
        ((gDelta_continuous_g.comp continuous_fst).mul
          (gDelta_continuous_g.comp continuous_snd))
    exact hcont.congr fun p => by
      simp only [Function.comp_apply, WordLift.equivProd, Equiv.coe_fn_mk,
        WordLift.mul_u, WordLift.mul_g, Units.smul_def, smul_eq_mul]
  continuous_inv := by
    refine continuous_induced_rng.mpr ?_
    have hcont : Continuous fun p : WordLift ℤ_[2] ℤ_[2]ˣ =>
        ((-(((p.g⁻¹ : ℤ_[2]ˣ) : ℤ_[2]) * p.u), p.g⁻¹) : ℤ_[2] × ℤ_[2]ˣ) :=
      (((Units.continuous_val.comp (continuous_inv.comp gDelta_continuous_g)).mul
        gDelta_continuous_u).neg).prodMk (continuous_inv.comp gDelta_continuous_g)
    exact hcont.congr fun p => by
      simp only [Function.comp_apply, WordLift.equivProd, Equiv.coe_fn_mk,
        WordLift.inv_u, WordLift.inv_g, Units.smul_def, smul_eq_mul]

attribute [local instance 2000] gDeltaTopGroup

/-- The lift group is compact.  File-local instance; see §1's warning. -/
theorem gDeltaCompact : CompactSpace (WordLift ℤ_[2] ℤ_[2]ˣ) :=
  gDeltaHomeo.symm.compactSpace

/-- The lift group is Hausdorff.  File-local instance; see §1's warning. -/
theorem gDeltaT2 : T2Space (WordLift ℤ_[2] ℤ_[2]ˣ) :=
  gDeltaHomeo.isEmbedding.t2Space

/-- The lift group is totally disconnected.  File-local instance; see §1's warning. -/
theorem gDeltaTotDisc : TotallyDisconnectedSpace (WordLift ℤ_[2] ℤ_[2]ˣ) := by
  refine ⟨fun t _ ht => ?_⟩
  intro x hx y hy
  have himg : IsPreconnected
      ((WordLift.equivProd (A := ℤ_[2]) (C := ℤ_[2]ˣ)) '' t) :=
    ht.image _ gDelta_continuous_equivProd.continuousOn
  have hsub : ((WordLift.equivProd (A := ℤ_[2]) (C := ℤ_[2]ˣ)) '' t).Subsingleton :=
    isTotallyDisconnected_of_totallyDisconnectedSpace _ _ (Set.subset_univ _) himg
  exact (WordLift.equivProd (A := ℤ_[2]) (C := ℤ_[2]ˣ)).injective
    (hsub ⟨x, hx, rfl⟩ ⟨y, hy, rfl⟩)

attribute [local instance 2000] gDeltaCompact gDeltaT2 gDeltaTotDisc

/-- The derivation component of a power is the geometric sum against the base
character value (`WordLift.pow_u` with the `Units`-action unfolded). -/
theorem gDelta_pow_u (p : WordLift ℤ_[2] ℤ_[2]ˣ) (n : ℕ) :
    (p ^ n).u = normSum (p.g : ℤ_[2]) n * p.u := by
  rw [WordLift.pow_u, normSum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [Units.smul_def, smul_eq_mul, Units.val_pow_eq_pow_val]

/-- `2^k` divides the geometric sum of length `2^k` of any unit: doubling the length
multiplies the sum by the even factor `1 + u^{2^k}`. -/
theorem gDelta_two_pow_dvd_normSum (u : ℤ_[2]ˣ) (k : ℕ) :
    (2 : ℤ_[2]) ^ k ∣ normSum (u : ℤ_[2]) (2 ^ k) := by
  induction k with
  | zero => simp [normSum]
  | succ k ih =>
    have hsplit : normSum (u : ℤ_[2]) (2 ^ (k + 1))
        = normSum (u : ℤ_[2]) (2 ^ k) * (1 + (u : ℤ_[2]) ^ 2 ^ k) := by
      rw [normSum, normSum, pow_succ, mul_two, Finset.sum_range_add]
      have hshift : ∀ i, (u : ℤ_[2]) ^ (2 ^ k + i)
          = (u : ℤ_[2]) ^ 2 ^ k * (u : ℤ_[2]) ^ i := fun i => pow_add _ _ _
      simp only [hshift, ← Finset.mul_sum]
      ring
    have heven : (2 : ℤ_[2]) ∣ 1 + (u : ℤ_[2]) ^ 2 ^ k := by
      obtain ⟨t, ht⟩ :=
        two_dvd_sub_of_isUnit ((Units.isUnit u).pow (2 ^ k)) isUnit_one.neg
      exact ⟨t, by linear_combination ht⟩
    rw [hsplit, pow_succ]
    exact mul_dvd_mul ih heven

/-- Any open neighbourhood of `1` in `ℤ₂ˣ` absorbs all units close to `1` in the
divisibility sense (both coordinates of the `Units` topology are controlled by
`2^n ∣ u − 1`). -/
theorem gDelta_units_ball_subset {B : Set ℤ_[2]ˣ} (hB : IsOpen B)
    (h1 : (1 : ℤ_[2]ˣ) ∈ B) :
    ∃ n : ℕ, ∀ w : ℤ_[2]ˣ, (2 : ℤ_[2]) ^ n ∣ (w : ℤ_[2]) - 1 → w ∈ B := by
  obtain ⟨W, hWopen, hWpre⟩ :=
    (Units.isInducing_embedProduct (M := ℤ_[2])).isOpen_iff.mp hB
  have h1W : ((1 : ℤ_[2]), MulOpposite.op (1 : ℤ_[2])) ∈ W := by
    have hmem : (1 : ℤ_[2]ˣ) ∈ Units.embedProduct ℤ_[2] ⁻¹' W := by
      rw [hWpre]; exact h1
    simpa [Units.embedProduct_apply] using hmem
  obtain ⟨A, B', hA, hB', h1A, h1B', hABW⟩ := isOpen_prod_iff.mp hWopen _ _ h1W
  obtain ⟨ε₁, hε₁, hballA⟩ := Metric.isOpen_iff.mp hA _ h1A
  have hB'' : IsOpen (MulOpposite.op ⁻¹' B' : Set ℤ_[2]) :=
    hB'.preimage MulOpposite.continuous_op
  have h1B'' : (1 : ℤ_[2]) ∈ MulOpposite.op ⁻¹' B' := h1B'
  obtain ⟨ε₂, hε₂, hballB⟩ := Metric.isOpen_iff.mp hB'' _ h1B''
  obtain ⟨K, hK⟩ := exists_pow_lt_of_lt_one (lt_min hε₁ hε₂) (by norm_num : (2:ℝ)⁻¹ < 1)
  have hlt : ((2 : ℕ) : ℝ) ^ (-((K : ℕ) : ℤ)) < min ε₁ ε₂ := by
    have heq : ((2 : ℕ) : ℝ) ^ (-((K : ℕ) : ℤ)) = ((2 : ℝ)⁻¹) ^ K := by
      rw [zpow_neg, ← inv_zpow, zpow_natCast]; norm_num
    rw [heq]; exact hK
  refine ⟨K, fun w hw => ?_⟩
  have hinv : (2 : ℤ_[2]) ^ K ∣ ((w⁻¹ : ℤ_[2]ˣ) : ℤ_[2]) - 1 := by
    obtain ⟨t, ht⟩ := hw
    have hc : ((w⁻¹ : ℤ_[2]ˣ) : ℤ_[2]) * (w : ℤ_[2]) = 1 := by
      rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
    exact ⟨-((w⁻¹ : ℤ_[2]ˣ) : ℤ_[2]) * t, by
      linear_combination (-((w⁻¹ : ℤ_[2]ˣ) : ℤ_[2])) * ht + hc⟩
  have hmemW : Units.embedProduct ℤ_[2] w ∈ W := by
    apply hABW
    rw [Units.embedProduct_apply]
    refine Set.mem_prod.mpr ⟨hballA ?_, hballB ?_⟩
    · rw [Metric.mem_ball]
      exact lt_of_le_of_lt (dist_one_le_of_two_pow_dvd hw)
        (lt_of_lt_of_le hlt (min_le_left _ _))
    · rw [Metric.mem_ball]
      exact lt_of_le_of_lt (dist_one_le_of_two_pow_dvd hinv)
        (lt_of_lt_of_le hlt (min_le_right _ _))
  have : w ∈ Units.embedProduct ℤ_[2] ⁻¹' W := hmemW
  rwa [hWpre] at this

/-- ⭐⭐ **The lift target is pro-2**: every finite continuous quotient of
`WordLift ℤ₂ ℤ₂ˣ` is a 2-group.  Uniform annihilation in both coordinates: the base
gains a level per squaring (`two_pow_succ_dvd_pow_two_pow_sub_one`), and the
derivation coordinate of `p^{2^K}` carries the geometric-sum factor, divisible by
`2^K` (`gDelta_two_pow_dvd_normSum`). -/
theorem gDelta_isProP : IsProP 2 (WordLift ℤ_[2] ℤ_[2]ˣ) := by
  intro U
  obtain ⟨W, hWopen, hWpre⟩ := isOpen_induced_iff.mp U.isOpen'
  have h1W : ((0 : ℤ_[2]), (1 : ℤ_[2]ˣ)) ∈ W := by
    have hmem : (1 : WordLift ℤ_[2] ℤ_[2]ˣ) ∈
        (WordLift.equivProd (A := ℤ_[2]) (C := ℤ_[2]ˣ)) ⁻¹' W := by
      rw [hWpre]; exact one_mem U.toSubgroup
    exact hmem
  obtain ⟨A, B, hA, hB, h0A, h1B, hABW⟩ := isOpen_prod_iff.mp hWopen _ _ h1W
  obtain ⟨n₁, hn₁⟩ := PropOneOne.exists_span_pow_subset hA h0A
  obtain ⟨n₂, hn₂⟩ := gDelta_units_ball_subset hB h1B
  intro q
  refine ⟨max n₁ n₂, ?_⟩
  obtain ⟨p, rfl⟩ := QuotientGroup.mk_surjective q
  show (QuotientGroup.mk' U.toSubgroup p) ^ 2 ^ max n₁ n₂ = 1
  rw [← map_pow, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  have hmem : p ^ 2 ^ max n₁ n₂ ∈
      (WordLift.equivProd (A := ℤ_[2]) (C := ℤ_[2]ˣ)) ⁻¹' W := by
    apply Set.mem_preimage.mpr
    apply hABW
    refine Set.mem_prod.mpr ⟨?_, ?_⟩
    · show (p ^ 2 ^ max n₁ n₂).u ∈ A
      rw [gDelta_pow_u]
      refine hn₁ ?_
      refine Ideal.mem_span_singleton.mpr (dvd_mul_of_dvd_left ?_ _)
      exact dvd_trans (pow_dvd_pow _ (le_max_left n₁ n₂))
        (gDelta_two_pow_dvd_normSum p.g (max n₁ n₂))
    · show (p ^ 2 ^ max n₁ n₂).g ∈ B
      rw [WordLift.pow_g]
      refine hn₂ _ ?_
      exact dvd_trans (pow_dvd_pow _ ((le_max_right n₁ n₂).trans (Nat.le_succ _)))
        (two_pow_succ_dvd_pow_two_pow_sub_one p.g (max n₁ n₂))
  have := hmem
  rw [hWpre] at this
  exact this

/-! ## §2 The functionals -/

section Functionals

variable {h : ℕ}

/-- The lift marking: the standard chi-values (`sqMark S X Y`, the mark of `chiSq`)
in the character slot, a free row `c` in the derivation slot. -/
noncomputable def gDeltaMark (h : ℕ) (c : Fin (sqRank h) → ℤ_[2]) :
    Fin (sqRank h) → WordLift ℤ_[2] ℤ_[2]ˣ :=
  fun i => ⟨c i, sqMark SvalUnit rootXUnit YvalUnit i⟩

@[simp] theorem gDeltaMark_zero (c : Fin (sqRank h) → ℤ_[2]) :
    gDeltaMark h c 0 = ⟨c 0, SvalUnit⟩ := by
  simp only [gDeltaMark, sqMark_zero]

@[simp] theorem gDeltaMark_one (c : Fin (sqRank h) → ℤ_[2]) :
    gDeltaMark h c 1 = ⟨c 1, rootXUnit⟩ := by
  simp only [gDeltaMark, sqMark_one]

@[simp] theorem gDeltaMark_two (c : Fin (sqRank h) → ℤ_[2]) :
    gDeltaMark h c 2 = ⟨c 2, YvalUnit⟩ := by
  simp only [gDeltaMark, sqMark_two]

@[simp] theorem gDeltaMark_handleU (c : Fin (sqRank h) → ℤ_[2]) (j : Fin h) :
    gDeltaMark h c (sqHandleIdxU j) = ⟨c (sqHandleIdxU j), 1⟩ := by
  simp only [gDeltaMark, sqMark_handleU]

@[simp] theorem gDeltaMark_handleV (c : Fin (sqRank h) → ℤ_[2]) (j : Fin h) :
    gDeltaMark h c (sqHandleIdxV j) = ⟨c (sqHandleIdxV j), 1⟩ := by
  simp only [gDeltaMark, sqMark_handleV]

/-- **The datum theorem at the committed orientation values** (Labute's Théorème 4
computation for the sq relator): the lifted rank-3 core word dies for *every* choice
of derivation values.  This is `isLabuteOrientationDatum_of_root` at the three ChiR
identities; the whole chi-twisted Fox row of the relator vanishes. -/
theorem gDelta_datum : IsLabuteOrientationDatum SvalUnit rootXUnit YvalUnit :=
  isLabuteOrientationDatum_of_root rootXUnit SvalUnit YvalUnit
    (by rw [val_rootXUnit]; exact rootX_isRoot)
    (by rw [val_SvalUnit, val_rootXUnit]; exact Sval_mul_denom)
    (by rw [val_YvalUnit, val_rootXUnit]; exact Yval_eq)

/-- **The relator dies at every lift marking**: the core factor by the datum theorem
(`sqWord` *is* `drWord`), the handle block by the handle lemma. -/
theorem gDelta_relWord_mark (c : Fin (sqRank h) → ℤ_[2]) :
    sqRelWord (gDeltaMark h c) = 1 := by
  have hU : (fun j => gDeltaMark h c (sqHandleIdxU j))
      = fun j => (⟨c (sqHandleIdxU j), 1⟩ : WordLift ℤ_[2] ℤ_[2]ˣ) := by
    funext j; exact gDeltaMark_handleU c j
  have hV : (fun j => gDeltaMark h c (sqHandleIdxV j))
      = fun j => (⟨c (sqHandleIdxV j), 1⟩ : WordLift ℤ_[2] ℤ_[2]ˣ) := by
    funext j; exact gDeltaMark_handleV c j
  rw [sqRelWord, hU, hV, handleWord_wordLift_one, mul_one, gDeltaMark_zero,
    gDeltaMark_one, gDeltaMark_two, sqWord_eq_drWord]
  exact gDelta_datum (c 0) (c 1) (c 2)

/-- ⭐⭐⭐ **The crossed homomorphism of the row `c`**: the continuous hom
`DSq h → WordLift ℤ₂ ℤ₂ˣ` with generator values `⟨c i, χ-mark i⟩`, through the
universal property `sqLiftHom` against the pro-2 structure of §1.  Its character
component is exactly `χ_sq` (`gDeltaHom_g`), so its derivation component `gDelta h c`
is a continuous crossed homomorphism `D` with `D(x y) = D x + χ_sq(x) D y` and
`D(sqGen i) = c i` — Labute's `D` with arbitrarily prescribed generator values,
existing on the *quotient* because the twisted Fox row of the relator vanishes
(`gDelta_relWord_mark`). -/
noncomputable def gDeltaHom (h : ℕ) (c : Fin (sqRank h) → ℤ_[2]) :
    ContinuousMonoidHom (DSq h : Type) (WordLift ℤ_[2] ℤ_[2]ˣ) :=
  sqLiftHom h gDelta_isProP (gDeltaMark h c) (gDelta_relWord_mark c)

@[simp] theorem gDeltaHom_gen (c : Fin (sqRank h) → ℤ_[2]) (i : Fin (sqRank h)) :
    gDeltaHom h c (sqGen h i) = gDeltaMark h c i :=
  sqLiftHom_gen _ _ _ _ _

/-- **The functional of the row `c`**: the derivation component of `gDeltaHom`. -/
noncomputable def gDelta (h : ℕ) (c : Fin (sqRank h) → ℤ_[2])
    (x : (DSq h : Type)) : ℤ_[2] :=
  (gDeltaHom h c x).u

theorem gDelta_continuous (c : Fin (sqRank h) → ℤ_[2]) : Continuous (gDelta h c) :=
  gDelta_continuous_u.comp (gDeltaHom h c).continuous_toFun

@[simp] theorem gDelta_gen (c : Fin (sqRank h) → ℤ_[2]) (i : Fin (sqRank h)) :
    gDelta h c (sqGen h i) = c i := by
  simp only [gDelta, gDeltaHom_gen]
  rfl

/-- The generator values of `chiSq`, as one lemma (the mark of its construction). -/
theorem gDelta_chiSq_gen (i : Fin (sqRank h)) :
    chiSq h (sqGen h i) = sqMark SvalUnit rootXUnit YvalUnit i :=
  sqLiftHom_gen _ _ _ _ _

/-- The character projection of the lift group, as a continuous hom. -/
noncomputable def gDeltaBase :
    ContinuousMonoidHom (WordLift ℤ_[2] ℤ_[2]ˣ) ℤ_[2]ˣ where
  toFun := WordLift.g
  map_one' := rfl
  map_mul' _ _ := rfl
  continuous_toFun := gDelta_continuous_g

/-- ⭐⭐ **The twist of `gDeltaHom` is exactly `χ_sq`** — hom-extensionality on the
generators, where both sides carry the same mark. -/
theorem gDeltaHom_g (c : Fin (sqRank h) → ℤ_[2]) (x : (DSq h : Type)) :
    (gDeltaHom h c x).g = chiSq h x := by
  have hcomp : gDeltaBase.comp (gDeltaHom h c) = chiSq h := by
    refine dsq_hom_ext _ _ fun i => ?_
    show (gDeltaHom h c (sqGen h i)).g = chiSq h (sqGen h i)
    rw [gDeltaHom_gen, gDelta_chiSq_gen]
    rfl
  exact DFunLike.congr_fun hcomp x

/-- The value of `gDeltaHom`, componentwise. -/
theorem gDeltaHom_apply (c : Fin (sqRank h) → ℤ_[2]) (x : (DSq h : Type)) :
    gDeltaHom h c x = ⟨gDelta h c x, chiSq h x⟩ :=
  WordLift.ext rfl (gDeltaHom_g c x)

@[simp] theorem gDelta_one (c : Fin (sqRank h) → ℤ_[2]) :
    gDelta h c (1 : (DSq h : Type)) = 0 := by
  show (gDeltaHom h c 1).u = 0
  rw [map_one]
  rfl

/-- **The crossed product rule** `D(xy) = Dx + χ(x) · Dy`. -/
theorem gDelta_mul (c : Fin (sqRank h) → ℤ_[2]) (x y : (DSq h : Type)) :
    gDelta h c (x * y) = gDelta h c x + (chiSq h x : ℤ_[2]) * gDelta h c y := by
  show (gDeltaHom h c (x * y)).u = _
  rw [map_mul, WordLift.mul_u, gDeltaHom_g]
  simp only [Units.smul_def, smul_eq_mul]
  rfl

/-- **The crossed inverse rule** `D(x⁻¹) = −χ(x)⁻¹ · Dx`. -/
theorem gDelta_inv (c : Fin (sqRank h) → ℤ_[2]) (x : (DSq h : Type)) :
    gDelta h c x⁻¹ = -(((chiSq h x)⁻¹ : ℤ_[2]ˣ) * gDelta h c x) := by
  show (gDeltaHom h c x⁻¹).u = _
  rw [map_inv, WordLift.inv_u, gDeltaHom_g]
  simp only [Units.smul_def, smul_eq_mul]
  rfl

/-- **The power rule** `D(xⁿ) = N_n(χ(x)) · Dx` (Labute's norm projector, through the
committed `pow_wordLift`). -/
theorem gDelta_pow (c : Fin (sqRank h) → ℤ_[2]) (x : (DSq h : Type)) (n : ℕ) :
    gDelta h c (x ^ n) = normSum (chiSq h x : ℤ_[2]) n * gDelta h c x := by
  show (gDeltaHom h c (x ^ n)).u = _
  rw [map_pow, gDeltaHom_apply, pow_wordLift]

/-- Homomorphisms carry the repo bracket to the repo bracket. -/
theorem gDelta_map_commP {G H : Type*} [Group G] [Group H] {F : Type*} [FunLike F G H]
    [MonoidHomClass F G H] (φ : F) (a b : G) : φ (commP a b) = commP (φ a) (φ b) := by
  simp only [commP, map_mul, map_inv]

/-- **The commutator rule for the repo bracket** `commP x y = x⁻¹y⁻¹xy`:
`D[x,y] = χ(x)⁻¹(χ(y)⁻¹ − 1) · Dx + χ(y)⁻¹(1 − χ(x)⁻¹) · Dy` (the committed
`commP_wordLift`, read through `gDeltaHom`). -/
theorem gDelta_commP (c : Fin (sqRank h) → ℤ_[2]) (x y : (DSq h : Type)) :
    gDelta h c (commP x y)
      = (((chiSq h x)⁻¹ : ℤ_[2]ˣ) : ℤ_[2]) * ((((chiSq h y)⁻¹ : ℤ_[2]ˣ) : ℤ_[2]) - 1)
          * gDelta h c x
        + (((chiSq h y)⁻¹ : ℤ_[2]ˣ) : ℤ_[2]) * (1 - (((chiSq h x)⁻¹ : ℤ_[2]ˣ) : ℤ_[2]))
          * gDelta h c y := by
  show (gDeltaHom h c (commP x y)).u = _
  rw [gDelta_map_commP, gDeltaHom_apply, gDeltaHom_apply, commP_wordLift]

/-- **The commutator rule for the mathlib bracket** `⁅x, y⁆ = x y x⁻¹ y⁻¹`:
`D⁅x,y⁆ = (1 − χ(y)) · Dx + (χ(x) − 1) · Dy` — the clean form, with no prefactor. -/
theorem gDelta_commutatorElement (c : Fin (sqRank h) → ℤ_[2]) (x y : (DSq h : Type)) :
    gDelta h c ⁅x, y⁆
      = (1 - (chiSq h y : ℤ_[2])) * gDelta h c x
        + ((chiSq h x : ℤ_[2]) - 1) * gDelta h c y := by
  have hx : (((chiSq h x)⁻¹ : ℤ_[2]ˣ) : ℤ_[2]) * ((chiSq h x : ℤ_[2]ˣ) : ℤ_[2]) = 1 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hy : (((chiSq h y)⁻¹ : ℤ_[2]ˣ) : ℤ_[2]) * ((chiSq h y : ℤ_[2]ˣ) : ℤ_[2]) = 1 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  rw [commutatorElement_def, gDelta_mul, gDelta_mul, gDelta_mul, gDelta_inv, gDelta_inv]
  simp only [map_mul, map_inv, Units.val_mul]
  linear_combination
    ((-((chiSq h y : ℤ_[2]ˣ) : ℤ_[2])) * gDelta h c x - gDelta h c y) * hx
    + ((-(((chiSq h x : ℤ_[2]ˣ) : ℤ_[2]) * (((chiSq h x)⁻¹ : ℤ_[2]ˣ) : ℤ_[2])))
        * gDelta h c y) * hy

/-- A commutator with both slots chi-trivial is invisible to every functional. -/
theorem gDelta_commP_of_chi_one (c : Fin (sqRank h) → ℤ_[2]) {x y : (DSq h : Type)}
    (hx : chiSq h x = 1) (hy : chiSq h y = 1) : gDelta h c (commP x y) = 0 := by
  rw [gDelta_commP, hx, hy]
  simp

end Functionals

/-! ## §3 The filtration: Labute Lemma 4(1) -/

section Filtration

variable {h : ℕ}

/-- The set of elements with `2^n`-divisible value is closed. -/
theorem gDelta_isClosed_dvd_set (n : ℕ) :
    IsClosed {z : ℤ_[2] | (2 : ℤ_[2]) ^ n ∣ z} := by
  have hset : {z : ℤ_[2] | (2 : ℤ_[2]) ^ n ∣ z}
      = Metric.closedBall 0 (((2 : ℕ) : ℝ) ^ (-(n : ℤ))) := by
    ext z
    simp only [Set.mem_setOf_eq, Metric.mem_closedBall, dist_zero_right]
    rw [PadicInt.norm_le_pow_iff_mem_span_pow, Ideal.mem_span_singleton]
    have h2 : ((2 : ℕ) : ℤ_[2]) = (2 : ℤ_[2]) := by norm_num
    rw [h2]
  rw [hset]
  exact Metric.isClosed_closedBall

/-- The chi-shadow at depth `k+1`: the orientation value of a `λ_{k+1}`-element is
`≡ 1 mod 2^{k+1}` (oddness at `k = 0`, the committed units-shadow
`twoCentralSeries_units_le` at `k ≥ 1`, transported through functoriality). -/
theorem gDelta_chi_sub_one_dvd {k : ℕ} {v : (DSq h : Type)}
    (hv : v ∈ twoCentralSeries (DSq h : Type) (k + 1)) :
    (2 : ℤ_[2]) ^ (k + 1) ∣ ((chiSq h v : ℤ_[2]ˣ) : ℤ_[2]) - 1 := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · rw [zero_add, pow_one]
    exact two_dvd_sub_of_isUnit (Units.isUnit (chiSq h v)) isUnit_one
  · have hmem : chiSq h v ∈ twoCentralSeries ℤ_[2]ˣ (k + 1) :=
      map_twoCentralSeries_le (chiSq h).toMonoidHom (chiSq h).continuous_toFun (k + 1)
        (Subgroup.mem_map_of_mem _ hv)
    have hker := twoCentralSeries_units_le (k + 1) (by omega) hmem
    have hdvd := mem_ker_units_toZModPow_iff.mp hker
    refine dvd_trans (pow_dvd_pow _ (by omega : k + 1 ≤ k + 2)) ?_
    have h2 : ((2 : ℕ) : ℤ_[2]) = (2 : ℤ_[2]) := by norm_num
    rwa [h2] at hdvd

/-- ⭐⭐ **The filtration compatibility** (Labute Lemma 4(1), value-normalized):
`λ_{k+1}`-elements have `2^k`-divisible functional values, for every row.  Squares
double the value against the even factor `1 + χ`, and mathlib-brackets contribute
`(1 − χ(g)) Dv + (χ(v) − 1) Dg` with both factors controlled — the first by oddness
and induction, the second by the chi-shadow. -/
theorem gDelta_dvd_of_mem_twoCentral (c : Fin (sqRank h) → ℤ_[2]) (k : ℕ) :
    ∀ {x : (DSq h : Type)}, x ∈ twoCentralSeries (DSq h : Type) (k + 1) →
      (2 : ℤ_[2]) ^ k ∣ gDelta h c x := by
  induction k with
  | zero => intro x _; rw [pow_zero]; exact one_dvd _
  | succ k ih =>
    intro x hx
    rw [twoCentralSeries_succ _ (Nat.le_add_left 1 k)] at hx
    let M : Subgroup (DSq h : Type) :=
      { carrier := {y | (2 : ℤ_[2]) ^ (k + 1) ∣ gDelta h c y}
        one_mem' := by
          simp only [Set.mem_setOf_eq, gDelta_one]
          exact dvd_zero _
        mul_mem' := fun {a b} ha hb => by
          simp only [Set.mem_setOf_eq] at ha hb ⊢
          rw [gDelta_mul]
          exact dvd_add ha (hb.mul_left _)
        inv_mem' := fun {a} ha => by
          simp only [Set.mem_setOf_eq] at ha ⊢
          rw [gDelta_inv]
          exact dvd_neg.mpr (ha.mul_left _) }
    have hMclosed : IsClosed (M : Set (DSq h : Type)) :=
      IsClosed.preimage (gDelta_continuous c) (gDelta_isClosed_dvd_set (k + 1))
    have hle : twoCentralSucc (twoCentralSeries (DSq h : Type) (k + 1)) ≤ M := by
      refine Subgroup.topologicalClosure_minimal _ (sup_le ?_ ?_) hMclosed
      · refine (Subgroup.closure_le _).2 ?_
        rintro _ ⟨v, hv, rfl⟩
        show (2 : ℤ_[2]) ^ (k + 1) ∣ gDelta h c (v ^ 2)
        rw [gDelta_pow, normSum_two, pow_succ']
        have h2 : (2 : ℤ_[2]) ∣ 1 + ((chiSq h v : ℤ_[2]ˣ) : ℤ_[2]) := by
          obtain ⟨t, ht⟩ := two_dvd_sub_of_isUnit (Units.isUnit (chiSq h v)) isUnit_one
          exact ⟨t + 1, by linear_combination ht⟩
        exact mul_dvd_mul h2 (ih hv)
      · refine Subgroup.commutator_le.2 fun v hv g _ => ?_
        show (2 : ℤ_[2]) ^ (k + 1) ∣ gDelta h c ⁅v, g⁆
        rw [gDelta_commutatorElement]
        refine dvd_add ?_ ?_
        · rw [pow_succ']
          have h2 : (2 : ℤ_[2]) ∣ 1 - ((chiSq h g : ℤ_[2]ˣ) : ℤ_[2]) :=
            two_dvd_sub_of_isUnit isUnit_one (Units.isUnit (chiSq h g))
          exact mul_dvd_mul h2 (ih hv)
        · exact ((gDelta_chi_sub_one_dvd hv).mul_right _)
    exact hle hx

/-- **The `2I`-normalization**: with a row in `2ℤ₂`, every value lands in `2ℤ₂`
(Labute's `D(F) ⊆ 2I`), and the filtration bound of
`gDelta_dvd_of_mem_twoCentral` sharpens by one power throughout. -/
theorem gDelta_two_dvd (c : Fin (sqRank h) → ℤ_[2])
    (hc : ∀ i, (2 : ℤ_[2]) ∣ c i) (x : (DSq h : Type)) :
    (2 : ℤ_[2]) ∣ gDelta h c x := by
  let M : Subgroup (DSq h : Type) :=
    { carrier := {y | (2 : ℤ_[2]) ^ 1 ∣ gDelta h c y}
      one_mem' := by
        simp only [Set.mem_setOf_eq, gDelta_one]
        exact dvd_zero _
      mul_mem' := fun {a b} ha hb => by
        simp only [Set.mem_setOf_eq] at ha hb ⊢
        rw [gDelta_mul]
        exact dvd_add ha (hb.mul_left _)
      inv_mem' := fun {a} ha => by
        simp only [Set.mem_setOf_eq] at ha ⊢
        rw [gDelta_inv]
        exact dvd_neg.mpr (ha.mul_left _) }
  have hMclosed : IsClosed (M : Set (DSq h : Type)) :=
    IsClosed.preimage (gDelta_continuous c) (gDelta_isClosed_dvd_set 1)
  have hle : (Subgroup.closure (Set.range (sqGen h))).topologicalClosure ≤ M := by
    refine Subgroup.topologicalClosure_minimal _ ((Subgroup.closure_le _).2 ?_) hMclosed
    rintro _ ⟨i, rfl⟩
    show (2 : ℤ_[2]) ^ 1 ∣ gDelta h c (sqGen h i)
    rw [gDelta_gen, pow_one]
    exact hc i
  rw [dsq_topGen] at hle
  have := hle (Subgroup.mem_top x)
  rwa [show (x ∈ M) = ((2 : ℤ_[2]) ^ 1 ∣ gDelta h c x) from rfl, pow_one] at this

/-- **Lift independence of the layer reading**: two elements with the same class in
`Q_{k+1}` have `2^k`-equal values, so `2^k ∣ gDelta` is a statement about classes. -/
theorem gDelta_dvd_of_levelMk_eq (c : Fin (sqRank h) → ℤ_[2]) {k : ℕ}
    {x y : (DSq h : Type)}
    (hxy : levelMk (DSq h : Type) (k + 1) x = levelMk (DSq h : Type) (k + 1) y)
    (hy : (2 : ℤ_[2]) ^ k ∣ gDelta h c y) : (2 : ℤ_[2]) ^ k ∣ gDelta h c x := by
  have hz : x * y⁻¹ ∈ twoCentralSeries (DSq h : Type) (k + 1) := by
    have h1 : levelMk (DSq h : Type) (k + 1) (x * y⁻¹) = 1 := by
      rw [map_mul, map_inv, hxy, mul_inv_cancel]
    exact (QuotientGroup.eq_one_iff _).mp h1
  have hx : x = x * y⁻¹ * y := by group
  rw [hx, gDelta_mul]
  exact dvd_add (gDelta_dvd_of_mem_twoCentral c k hz) (hy.mul_left _)

end Filtration

/-! ## §4 The towers: Labute Lemma 4(3), and the excluded letter -/

section Towers

variable {h : ℕ}

/-- The geometric identity `(u − 1) · N_n(u) = uⁿ − 1`, proved inline to stay
independent of the mathlib `GeomSum` file location. -/
theorem gDelta_sub_one_mul_normSum (u : ℤ_[2]) (n : ℕ) :
    (u - 1) * normSum u n = u ^ n - 1 := by
  induction n with
  | zero => simp [normSum]
  | succ n ih =>
    rw [normSum, Finset.sum_range_succ, ← normSum]
    ring_nf
    ring_nf at ih
    linear_combination ih

/-- **The unit-valuation of the tower coefficient**: if `v₂(u − 1) = s` exactly with
`2 ≤ s`, then `N_{2^m}(u) = 2^m · unit` — the level grows by exactly one per
squaring (the committed `exists_unit_pow_two_pow_sub_one_of_level`). -/
theorem gDelta_normSum_unit {u a : ℤ_[2]ˣ} {s : ℕ} (hs : 2 ≤ s)
    (hu : (u : ℤ_[2]) - 1 = 2 ^ s * a) (m : ℕ) :
    ∃ w : ℤ_[2]ˣ, normSum (u : ℤ_[2]) (2 ^ m) = 2 ^ m * w := by
  obtain ⟨b, hb⟩ := exists_unit_pow_two_pow_sub_one_of_level u a s hs hu m
  refine ⟨b * a⁻¹, ?_⟩
  have hne : (2 : ℤ_[2]) ^ s * (a : ℤ_[2]) ≠ 0 :=
    mul_ne_zero (pow_ne_zero _ (by norm_num)) (Units.ne_zero a)
  apply mul_right_cancel₀ hne
  have hgeom := gDelta_sub_one_mul_normSum (u : ℤ_[2]) (2 ^ m)
  rw [hu] at hgeom
  rw [Units.val_pow_eq_pow_val] at hb
  have hcanc : ((a⁻¹ : ℤ_[2]ˣ) : ℤ_[2]) * (a : ℤ_[2]) = 1 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  rw [Units.val_mul]
  linear_combination hgeom + hb - ((2 : ℤ_[2]) ^ (m + s) * (b : ℤ_[2])) * hcanc

/-- `X − 1 = 4 · unit` (`X ≡ 5 mod 16`). -/
theorem gDelta_rootX_sub_one : ∃ a : ℤ_[2]ˣ, rootX - 1 = 2 ^ 2 * a := by
  have h5 : PadicInt.toZModPow 4 (rootX - 5) = 0 := by
    rw [map_sub, rootX_toZModPow_four, map_ofNat]
    exact sub_self _
  have hmem : rootX - 5 ∈ RingHom.ker (PadicInt.toZModPow (p := 2) 4) := h5
  rw [PadicInt.ker_toZModPow, Ideal.mem_span_singleton] at hmem
  obtain ⟨t, ht⟩ := hmem
  refine ⟨(isUnit_one_add_two_mul (2 * t)).unit, ?_⟩
  rw [IsUnit.unit_spec]
  have h2 : ((2 : ℕ) : ℤ_[2]) = (2 : ℤ_[2]) := by norm_num
  rw [h2] at ht
  linear_combination ht

/-- `S − 1 = 4 · unit` (`S ≡ 13 mod 16`). -/
theorem gDelta_Sval_sub_one : ∃ a : ℤ_[2]ˣ, Sval - 1 = 2 ^ 2 * a := by
  have h13 : PadicInt.toZModPow 4 (Sval - 13) = 0 := by
    rw [map_sub, Sval_toZModPow_four, map_ofNat]
    exact sub_self _
  have hmem : Sval - 13 ∈ RingHom.ker (PadicInt.toZModPow (p := 2) 4) := h13
  rw [PadicInt.ker_toZModPow, Ideal.mem_span_singleton] at hmem
  obtain ⟨t, ht⟩ := hmem
  refine ⟨(isUnit_one_add_two_mul (1 + 2 * t)).unit, ?_⟩
  rw [IsUnit.unit_spec]
  have h2 : ((2 : ℕ) : ℤ_[2]) = (2 : ℤ_[2]) := by norm_num
  rw [h2] at ht
  linear_combination ht

/-- `S − X = 8 · unit` (`S − X ≡ 8 mod 16`) — the congruence behind the core
defect's exact reading in §6. -/
theorem gDelta_Sval_sub_rootX : ∃ w : ℤ_[2]ˣ, Sval - rootX = 2 ^ 3 * w := by
  have h8 : PadicInt.toZModPow 4 (Sval - rootX - 8) = 0 := by
    rw [map_sub, map_sub, Sval_toZModPow_four, rootX_toZModPow_four, map_ofNat]
    decide
  have hmem : Sval - rootX - 8 ∈ RingHom.ker (PadicInt.toZModPow (p := 2) 4) := h8
  rw [PadicInt.ker_toZModPow, Ideal.mem_span_singleton] at hmem
  obtain ⟨t, ht⟩ := hmem
  refine ⟨(isUnit_one_add_two_mul t).unit, ?_⟩
  rw [IsUnit.unit_spec]
  have h2 : ((2 : ℕ) : ℤ_[2]) = (2 : ℤ_[2]) := by norm_num
  rw [h2] at ht
  linear_combination ht

/-- ⭐ **The `σ`-tower formula**: `gDelta h c (σ^{2^m}) = 2^m · unit · c 0`. -/
theorem gDelta_sigma_tower (c : Fin (sqRank h) → ℤ_[2]) (m : ℕ) :
    ∃ w : ℤ_[2]ˣ, gDelta h c (dsqSigma h ^ 2 ^ m) = 2 ^ m * w * c 0 := by
  obtain ⟨a, ha⟩ := gDelta_Sval_sub_one
  have ha' : ((SvalUnit : ℤ_[2]ˣ) : ℤ_[2]) - 1 = 2 ^ 2 * a := by
    rw [val_SvalUnit]; exact ha
  obtain ⟨w, hw⟩ := gDelta_normSum_unit le_rfl ha' m
  refine ⟨w, ?_⟩
  rw [gDelta_pow, chiSq_sigma, hw]
  have hval : gDelta h c (dsqSigma h) = c 0 := gDelta_gen c 0
  rw [hval]

/-- ⭐ **The `x₀`-tower formula**: `gDelta h c (x₀^{2^m}) = 2^m · unit · c 1`. -/
theorem gDelta_x0_tower (c : Fin (sqRank h) → ℤ_[2]) (m : ℕ) :
    ∃ w : ℤ_[2]ˣ, gDelta h c (dsqX0 h ^ 2 ^ m) = 2 ^ m * w * c 1 := by
  obtain ⟨a, ha⟩ := gDelta_rootX_sub_one
  have ha' : ((rootXUnit : ℤ_[2]ˣ) : ℤ_[2]) - 1 = 2 ^ 2 * a := by
    rw [val_rootXUnit]; exact ha
  obtain ⟨w, hw⟩ := gDelta_normSum_unit le_rfl ha' m
  refine ⟨w, ?_⟩
  rw [gDelta_pow, chiSq_x0, hw]
  have hval : gDelta h c (dsqX0 h) = c 1 := gDelta_gen c 1
  rw [hval]

/-- **The handle-tower formula, exact**: `gDelta h c (u_j^{2^m}) = 2^m · c(u_j)` —
the chi-trivial letters have geometric sum exactly `2^m`. -/
theorem gDelta_handleU_tower (c : Fin (sqRank h) → ℤ_[2]) (j : Fin h) (m : ℕ) :
    gDelta h c (sqGen h (sqHandleIdxU j) ^ 2 ^ m) = 2 ^ m * c (sqHandleIdxU j) := by
  rw [gDelta_pow, chiSq_handleU, gDelta_gen, Units.val_one, normSum_one_base]
  push_cast
  ring

/-- Two divides no unit. -/
theorem gDelta_not_two_dvd_unit (w : ℤ_[2]ˣ) : ¬ (2 : ℤ_[2]) ∣ (w : ℤ_[2]) := by
  intro hdvd
  obtain ⟨t, ht⟩ := two_dvd_sub_of_isUnit (Units.isUnit w) isUnit_one
  have h1 : (2 : ℤ_[2]) ∣ 1 := by
    obtain ⟨s, hs⟩ := hdvd
    exact ⟨s - t, by linear_combination hs - ht⟩
  have hunit : IsUnit (2 : ℤ_[2]) := isUnit_of_dvd_one h1
  have hnorm := PadicInt.isUnit_iff.mp hunit
  have h2 : ((2 : ℕ) : ℤ_[2]) = (2 : ℤ_[2]) := by norm_num
  rw [← h2, PadicInt.norm_p] at hnorm
  norm_num at hnorm

/-- ⭐⭐ **The `σ`-tower survives every level**: `σ^{2^m} ∉ λ_{m+2}` — the row `e₀`
reads the tower at exactly the layer bit, against the filtration bound. -/
theorem gDelta_sigma_tower_notMem (m : ℕ) :
    dsqSigma h ^ 2 ^ m ∉ twoCentralSeries (DSq h : Type) (m + 2) := by
  intro hmem
  classical
  set c : Fin (sqRank h) → ℤ_[2] := fun i => if i = 0 then 1 else 0 with hc
  have hdvd := gDelta_dvd_of_mem_twoCentral c (m + 1) hmem
  obtain ⟨w, hw⟩ := gDelta_sigma_tower c m
  rw [hw] at hdvd
  have hc0 : c 0 = 1 := by simp [hc]
  rw [hc0, mul_one, pow_succ] at hdvd
  obtain ⟨t, ht⟩ := hdvd
  have hcancel : (w : ℤ_[2]) = 2 * t := by
    have hne : (2 : ℤ_[2]) ^ m ≠ 0 := pow_ne_zero _ (by norm_num)
    apply mul_left_cancel₀ hne
    linear_combination ht
  exact gDelta_not_two_dvd_unit w ⟨t, hcancel⟩

/-- ⭐⭐ **The `x₀`-tower survives every level**: `x₀^{2^m} ∉ λ_{m+2}`. -/
theorem gDelta_x0_tower_notMem (m : ℕ) :
    dsqX0 h ^ 2 ^ m ∉ twoCentralSeries (DSq h : Type) (m + 2) := by
  intro hmem
  classical
  set c : Fin (sqRank h) → ℤ_[2] := fun i => if i = 1 then 1 else 0 with hc
  have hdvd := gDelta_dvd_of_mem_twoCentral c (m + 1) hmem
  obtain ⟨w, hw⟩ := gDelta_x0_tower c m
  rw [hw] at hdvd
  have hc1 : c 1 = 1 := by simp [hc]
  rw [hc1, mul_one, pow_succ] at hdvd
  obtain ⟨t, ht⟩ := hdvd
  have hcancel : (w : ℤ_[2]) = 2 * t := by
    have hne : (2 : ℤ_[2]) ^ m ≠ 0 := pow_ne_zero _ (by norm_num)
    apply mul_left_cancel₀ hne
    linear_combination ht
  exact gDelta_not_two_dvd_unit w ⟨t, hcancel⟩

/-- ⭐⭐ **The handle towers survive every level**: `u_j^{2^m} ∉ λ_{m+2}`. -/
theorem gDelta_handleU_tower_notMem (j : Fin h) (m : ℕ) :
    sqGen h (sqHandleIdxU j) ^ 2 ^ m ∉ twoCentralSeries (DSq h : Type) (m + 2) := by
  intro hmem
  classical
  set c : Fin (sqRank h) → ℤ_[2] := fun i => if i = sqHandleIdxU j then 1 else 0 with hc
  have hdvd := gDelta_dvd_of_mem_twoCentral c (m + 1) hmem
  rw [gDelta_handleU_tower] at hdvd
  have hcU : c (sqHandleIdxU j) = 1 := by simp [hc]
  rw [hcU, mul_one, pow_succ] at hdvd
  obtain ⟨t, ht⟩ := hdvd
  have hcancel : (1 : ℤ_[2]) = 2 * t := by
    have hne : (2 : ℤ_[2]) ^ m ≠ 0 := pow_ne_zero _ (by norm_num)
    apply mul_left_cancel₀ hne
    linear_combination ht
  exact gDelta_not_two_dvd_unit 1 (by rw [Units.val_one]; exact ⟨t, hcancel⟩)

/-- `X² + 1 = 2 · unit` — the first step of the `Y`-column collapse (`Y = −X²`). -/
theorem gDelta_rootX_sq_add_one : ∃ a : ℤ_[2]ˣ, rootX ^ 2 + 1 = 2 * a := by
  obtain ⟨b, hb⟩ := gDelta_rootX_sub_one
  refine ⟨(isUnit_one_add_two_mul (2 * (b : ℤ_[2]) + 4 * (b : ℤ_[2]) ^ 2)).unit, ?_⟩
  rw [IsUnit.unit_spec]
  linear_combination (rootX + 1 + 4 * (b : ℤ_[2])) * hb

/-- `Y² − 1 = 16 · unit`: `Y² = X⁴` and `X⁴ − 1 = (X−1)(X+1)(X²+1)` has valuation
`2 + 1 + 1 = 4` exactly. -/
theorem gDelta_Yval_sq_sub_one : ∃ a : ℤ_[2]ˣ, Yval ^ 2 - 1 = 2 ^ 4 * a := by
  obtain ⟨b, hb⟩ := gDelta_rootX_sub_one
  obtain ⟨d, hd⟩ := gDelta_rootX_sq_add_one
  have hplus : rootX + 1 = 2 * (1 + 2 * (b : ℤ_[2])) := by linear_combination hb
  refine ⟨b * (isUnit_one_add_two_mul (b : ℤ_[2])).unit * d, ?_⟩
  have hY2 : Yval ^ 2 = rootX ^ 4 := by rw [Yval_eq]; ring
  rw [hY2, Units.val_mul, Units.val_mul, IsUnit.unit_spec]
  have hfact : rootX ^ 4 - 1 = (rootX - 1) * (rootX + 1) * (rootX ^ 2 + 1) := by ring
  rw [hfact, hb, hplus, hd]
  ring

/-- ⭐⭐ **The excluded letter** (Labute's `k ≠ 2` side condition): the `x₁`-tower is
invisible to *every* functional, two levels deeper than the reading bit —
`2^{m+2} ∣ gDelta h c (x₁^{2^m})` for `m ≥ 1` and every row `c`.  The mechanism is
`χ(x₁) = Y ≡ 3 mod 4`: the geometric sum `N_{2^m}(Y) = (Y^{2^m} − 1)/(Y − 1)` has
valuation `(m − 1) + 4 − 1 = m + 2`. -/
theorem gDelta_x1_tower_dvd (c : Fin (sqRank h) → ℤ_[2]) {m : ℕ} (hm : 1 ≤ m) :
    (2 : ℤ_[2]) ^ (m + 2) ∣ gDelta h c (dsqX1 h ^ 2 ^ m) := by
  rw [gDelta_pow, chiSq_x1, val_YvalUnit]
  refine Dvd.dvd.mul_right ?_ _
  -- N_{2^m}(Y) · (Y − 1) = Y^{2^m} − 1 = (Y²)^{2^{m−1}} − 1 = 2^{(m−1)+4} · unit,
  -- and Y − 1 = −(X²+1) = −2·unit, so N = 2^{m+2} · unit.
  obtain ⟨a, ha⟩ := gDelta_Yval_sq_sub_one
  obtain ⟨d, hd⟩ := gDelta_rootX_sq_add_one
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  have hsq : ((YvalUnit ^ 2 : ℤ_[2]ˣ) : ℤ_[2]) - 1 = 2 ^ 4 * a := by
    rw [Units.val_pow_eq_pow_val, val_YvalUnit]
    exact ha
  obtain ⟨b, hb⟩ := exists_unit_pow_two_pow_sub_one_of_level (YvalUnit ^ 2) a 4
    (by norm_num) hsq m'
  have hYm : Yval ^ 2 ^ (m' + 1) - 1 = 2 ^ (m' + 4) * (b : ℤ_[2]) := by
    have hpow : ((YvalUnit ^ 2) ^ 2 ^ m' : ℤ_[2]ˣ) = YvalUnit ^ 2 ^ (m' + 1) := by
      rw [← pow_mul, ← pow_succ']
    rw [hpow, Units.val_pow_eq_pow_val, val_YvalUnit] at hb
    exact hb
  have hgeom := gDelta_sub_one_mul_normSum Yval (2 ^ (m' + 1))
  have hsub : Yval - 1 = -(2 * (d : ℤ_[2])) := by
    rw [Yval_eq]
    linear_combination -hd
  have hne : Yval - 1 ≠ 0 := by
    rw [hsub]
    exact neg_ne_zero.mpr (mul_ne_zero (by norm_num) (Units.ne_zero d))
  have hcanc : ((d⁻¹ : ℤ_[2]ˣ) : ℤ_[2]) * (d : ℤ_[2]) = 1 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  refine ⟨-(((d⁻¹ : ℤ_[2]ˣ) : ℤ_[2]) * (b : ℤ_[2])), ?_⟩
  apply mul_left_cancel₀ hne
  rw [hgeom, hYm, hsub]
  linear_combination (-(2 : ℤ_[2]) ^ (m' + 4) * (b : ℤ_[2])) * hcanc

end Towers

/-! ## §5 Vanishing on the defects: Labute Lemma 4(2) -/

section Vanishing

variable {h : ℕ}

/-- Pivot powers are chi-trivial (`chiSq_sqPivot` through `zpowZtwo`-naturality). -/
theorem gDelta_chiSq_zpow_pivot (a : ℤ_[2]) :
    chiSq h (zpowZtwo (isProP_DSq h) (sqPivot h) a) = 1 := by
  rw [map_zpowZtwo (isProP_DSq h) isProP_two_unitsPadicInt (chiSq h), chiSq_sqPivot,
    zpowZtwo_one_base]

/-- Handle-letter powers are chi-trivial. -/
theorem gDelta_chiSq_zpow_handleU (j : Fin h) (a : ℤ_[2]) :
    chiSq h (zpowZtwo (isProP_DSq h) (sqGen h (sqHandleIdxU j)) a) = 1 := by
  rw [map_zpowZtwo (isProP_DSq h) isProP_two_unitsPadicInt (chiSq h), chiSq_handleU,
    zpowZtwo_one_base]

theorem gDelta_chiSq_zpow_handleV (j : Fin h) (a : ℤ_[2]) :
    chiSq h (zpowZtwo (isProP_DSq h) (sqGen h (sqHandleIdxV j)) a) = 1 := by
  rw [map_zpowZtwo (isProP_DSq h) isProP_two_unitsPadicInt (chiSq h), chiSq_handleV,
    zpowZtwo_one_base]

/-- The Eichler-cleared `u`-letter is chi-trivial. -/
theorem gDelta_chiSq_sqEichU
    (nu' : ContinuousMonoidHom (DSq h : Type) (Multiplicative ℤ_[2])) (j : Fin h) :
    chiSq h (sqEichU h nu' j) = 1 := by
  rw [sqEichU, map_mul, map_inv, gDelta_chiSq_zpow_pivot, inv_one, one_mul,
    chiSq_handleU]

/-- The Eichler-cleared `v`-letter is chi-trivial. -/
theorem gDelta_chiSq_sqEichV
    (nu' : ContinuousMonoidHom (DSq h : Type) (Multiplicative ℤ_[2])) (j : Fin h) :
    chiSq h (sqEichV h nu' j) = 1 := by
  rw [sqEichV, map_mul, map_inv, gDelta_chiSq_zpow_pivot, inv_one, mul_one,
    chiSq_handleV]

/-- ⭐ **The wave-68 dressing is a kernel-of-chi element** — the pivot factor and both
handle factors are chi-trivial.  This is the committed-side form of Labute's dressing
by elements of `X = ker χ`, and it is what makes the §5 kills apply to the committed
route. -/
theorem gDelta_chiSq_bridgeDress
    (nu' : ContinuousMonoidHom (DSq h : Type) (Multiplicative ℤ_[2])) (j : Fin h) :
    chiSq h (bridgeDress nu' j) = 1 := by
  rw [bridgeDress, map_mul, map_mul, gDelta_chiSq_zpow_handleU,
    gDelta_chiSq_zpow_handleV, gDelta_chiSq_zpow_pivot, mul_one, mul_one]

theorem gDelta_chiSq_bridgeTuple
    (nu' : ContinuousMonoidHom (DSq h : Type) (Multiplicative ℤ_[2])) (j : Fin h)
    (i : Fin (sqRank h)) : chiSq h (bridgeTuple nu' j i) = 1 := by
  simp only [bridgeTuple]
  split_ifs
  · exact gDelta_chiSq_bridgeDress nu' j
  · exact gDelta_chiSq_bridgeDress nu' j
  · exact map_one _

/-- The undressed frame carries the standard chi-values. -/
theorem gDelta_chiFrame_arbBase
    (nu' : ContinuousMonoidHom (DSq h : Type) (Multiplicative ℤ_[2])) (j : Fin h)
    (i : Fin (sqRank h)) :
    chiSq h (sqArbBase h nu' j i) = sqMark SvalUnit rootXUnit YvalUnit i := by
  rcases sqIdx_cases i with rfl | rfl | rfl | ⟨j', rfl⟩ | ⟨j', rfl⟩
  · rw [sqArbBase_zero, sqMark_zero]; exact chiSq_sigma h
  · rw [sqArbBase_one, sqMark_one]; exact chiSq_x0 h
  · rw [sqArbBase_two, sqMark_two]; exact chiSq_x1 h
  · by_cases hjj : j' = j
    · subst hjj
      rw [sqArbBase_handleU, sqMark_handleU]
      exact gDelta_chiSq_sqEichU nu' j'
    · rw [sqArbBase_handleU_ne hjj, sqMark_handleU]
      exact chiSq_handleU h j'
  · by_cases hjj : j' = j
    · subst hjj
      rw [sqArbBase_handleV, sqMark_handleV]
      exact gDelta_chiSq_sqEichV nu' j'
    · rw [sqArbBase_handleV_ne hjj, sqMark_handleV]
      exact chiSq_handleV h j'

/-- A kernel-of-chi dressing keeps the frame chi-standard. -/
theorem gDelta_chiFrame_dressed
    (nu' : ContinuousMonoidHom (DSq h : Type) (Multiplicative ℤ_[2])) (j : Fin h)
    {a : Fin (sqRank h) → (DSq h : Type)} (ha : ∀ i, chiSq h (a i) = 1)
    (i : Fin (sqRank h)) :
    chiSq h (sqArbFrame h nu' j a i) = sqMark SvalUnit rootXUnit YvalUnit i := by
  simp only [sqArbFrame, map_mul, ha i, mul_one]
  exact gDelta_chiFrame_arbBase nu' j i

/-- ⭐⭐⭐ **The master kill** (Labute Lemma 4(2): a dressed relator is a relator):
any frame with the standard chi-values has relator value invisible to `gDeltaHom` —
the lifted relator value is `1` on the nose, because the lifted frame is again a lift
marking and the datum theorem applies verbatim. -/
theorem gDelta_relWord_of_chiFrame (c : Fin (sqRank h) → ℤ_[2])
    {m : Fin (sqRank h) → (DSq h : Type)}
    (hm : ∀ i, chiSq h (m i) = sqMark SvalUnit rootXUnit YvalUnit i) :
    gDeltaHom h c (sqRelWord m) = 1 := by
  rw [map_sqRelWord]
  have hfun : (fun i => gDeltaHom h c (m i))
      = gDeltaMark h (fun i => gDelta h c (m i)) := by
    funext i
    rw [gDeltaHom_apply, hm i]
    rfl
  rw [hfun, gDelta_relWord_mark]

/-- The functional form of the master kill. -/
theorem gDelta_relWord_of_chiFrame_eq_zero (c : Fin (sqRank h) → ℤ_[2])
    {m : Fin (sqRank h) → (DSq h : Type)}
    (hm : ∀ i, chiSq h (m i) = sqMark SvalUnit rootXUnit YvalUnit i) :
    gDelta h c (sqRelWord m) = 0 := by
  show (gDeltaHom h c (sqRelWord m)).u = 0
  rw [gDelta_relWord_of_chiFrame c hm]
  rfl

/-- ⭐⭐⭐ **The wave-68 leftover lift dies exactly**: the relator value of the
bridge-dressed frame is invisible to every functional — Labute's `D e₁ = 0` for the
committed class-four defect, at the group level (hence at every class at once). -/
theorem gDelta_leftover_lift (c : Fin (sqRank h) → ℤ_[2])
    (nu' : ContinuousMonoidHom (DSq h : Type) (Multiplicative ℤ_[2])) (j : Fin h) :
    gDelta h c (sqRelWord (sqArbFrame h nu' j (bridgeTuple nu' j))) = 0 :=
  gDelta_relWord_of_chiFrame_eq_zero c
    (gDelta_chiFrame_dressed nu' j (gDelta_chiSq_bridgeTuple nu' j))

/-- ⭐⭐⭐ **The interface Prop of the lane** (for the W75 assembly): every functional
kills the relator value of every kernel-of-chi dressing of every frame — the
level-generic defect shape that `SqClassClearingSupply` produces, for the dressings
the chi-trivial route provides.  Proved outright below. -/
def GDeltaDefectVanishing (h : ℕ) : Prop :=
  ∀ (c : Fin (sqRank h) → ℤ_[2])
    (nu' : ContinuousMonoidHom (DSq h : Type) (Multiplicative ℤ_[2])) (j : Fin h)
    (a : Fin (sqRank h) → (DSq h : Type)), (∀ i, chiSq h (a i) = 1) →
      gDelta h c (sqRelWord (sqArbFrame h nu' j a)) = 0

/-- ⭐⭐⭐ The interface Prop holds. -/
theorem gDeltaDefectVanishing_holds (h : ℕ) : GDeltaDefectVanishing h :=
  fun c nu' j _ ha =>
    gDelta_relWord_of_chiFrame_eq_zero c (gDelta_chiFrame_dressed nu' j ha)

/-- Every lift of `cfourIdLeftover` has `2^3`-divisible value: the canonical lift
dies exactly, and the reading is lift-independent. -/
theorem gDelta_dvd_of_levelMk_eq_leftover (c : Fin (sqRank h) → ℤ_[2])
    (nu' : ContinuousMonoidHom (DSq h : Type) (Multiplicative ℤ_[2])) (j : Fin h)
    {x : (DSq h : Type)}
    (hx : levelMk (DSq h : Type) 4 x = cfourIdLeftover nu' j) :
    (2 : ℤ_[2]) ^ 3 ∣ gDelta h c x := by
  have hlift : levelMk (DSq h : Type) 4 x
      = levelMk (DSq h : Type) 4 (sqRelWord (sqArbFrame h nu' j (bridgeTuple nu' j))) :=
    hx
  exact gDelta_dvd_of_levelMk_eq c (k := 3) hlift
    (by rw [gDelta_leftover_lift]; exact dvd_zero _)

/-- The canonical group-level lift of the class-four Eichler defect. -/
noncomputable def gDeltaEichLift
    (nu' : ContinuousMonoidHom (DSq h : Type) (Multiplicative ℤ_[2])) (j : Fin h) :
    (DSq h : Type) :=
  (commP (sqGen h (sqHandleIdxU j)) (sqGen h (sqHandleIdxV j)))⁻¹ *
    commP (sqEichU h nu' j) (sqEichV h nu' j)

theorem gDelta_eichLift_levelMk
    (nu' : ContinuousMonoidHom (DSq h : Type) (Multiplicative ℤ_[2])) (j : Fin h) :
    levelMk (DSq h : Type) 4 (gDeltaEichLift nu' j) = cfourEichDefect nu' j := by
  simp only [gDeltaEichLift, cfourEichDefect, map_mul, map_inv,
    cfourKnob_levelMk_commP]

/-- **The Eichler defect's lift dies exactly**: all four bracket slots are
chi-trivial. -/
theorem gDelta_eichLift_eq_zero (c : Fin (sqRank h) → ℤ_[2])
    (nu' : ContinuousMonoidHom (DSq h : Type) (Multiplicative ℤ_[2])) (j : Fin h) :
    gDelta h c (gDeltaEichLift nu' j) = 0 := by
  have h1 : gDelta h c (commP (sqGen h (sqHandleIdxU j)) (sqGen h (sqHandleIdxV j))) = 0 :=
    gDelta_commP_of_chi_one c (chiSq_handleU h j) (chiSq_handleV h j)
  have h2 : gDelta h c (commP (sqEichU h nu' j) (sqEichV h nu' j)) = 0 :=
    gDelta_commP_of_chi_one c (gDelta_chiSq_sqEichU nu' j) (gDelta_chiSq_sqEichV nu' j)
  rw [gDeltaEichLift, gDelta_mul, gDelta_inv, h1, h2]
  ring

/-- Every lift of `cfourEichDefect` has `2^3`-divisible value. -/
theorem gDelta_dvd_of_levelMk_eq_eichDefect (c : Fin (sqRank h) → ℤ_[2])
    (nu' : ContinuousMonoidHom (DSq h : Type) (Multiplicative ℤ_[2])) (j : Fin h)
    {x : (DSq h : Type)}
    (hx : levelMk (DSq h : Type) 4 x = cfourEichDefect nu' j) :
    (2 : ℤ_[2]) ^ 3 ∣ gDelta h c x := by
  have hlift : levelMk (DSq h : Type) 4 x
      = levelMk (DSq h : Type) 4 (gDeltaEichLift nu' j) := by
    rw [hx, gDelta_eichLift_levelMk]
  exact gDelta_dvd_of_levelMk_eq c (k := 3) hlift
    (by rw [gDelta_eichLift_eq_zero]; exact dvd_zero _)

end Vanishing

/-! ## §6 The core defect, sharply -/

section CoreDefect

variable {h : ℕ}

/-- The canonical group-level lift of `cfourDefCore`. -/
noncomputable def gDeltaCoreLift
    (nu' : ContinuousMonoidHom (DSq h : Type) (Multiplicative ℤ_[2])) (j : Fin h) :
    (DSq h : Type) :=
  commP (dsqSigma h) (bridgeDress nu' j) * commP (bridgeDress nu' j) (dsqX0 h) *
    gDeltaEichLift nu' j

theorem gDelta_coreLift_levelMk
    (nu' : ContinuousMonoidHom (DSq h : Type) (Multiplicative ℤ_[2])) (j : Fin h) :
    levelMk (DSq h : Type) 4 (gDeltaCoreLift nu' j) = cfourDefCore nu' j := by
  simp only [gDeltaCoreLift, cfourDefCore, map_mul, cfourKnob_levelMk_commP,
    gDelta_eichLift_levelMk]

/-- The orientation kills the repo bracket (commutative target). -/
theorem gDelta_chiSq_commP (x y : (DSq h : Type)) : chiSq h (commP x y) = 1 := by
  rw [gDelta_map_commP, commP_eq_one]

/-- ⭐⭐ **The core defect's exact reading**: on the canonical lift,
`gDelta = (X⁻¹ − S⁻¹) · gDelta(bridgeDress)`.  The core defect is *not* a pure
relator shape, and this is the honest value: it vanishes only up to
`v₂(S − X) = 3`. -/
theorem gDelta_coreLift_eq (c : Fin (sqRank h) → ℤ_[2])
    (nu' : ContinuousMonoidHom (DSq h : Type) (Multiplicative ℤ_[2])) (j : Fin h) :
    gDelta h c (gDeltaCoreLift nu' j)
      = (((rootXUnit⁻¹ : ℤ_[2]ˣ) : ℤ_[2]) - ((SvalUnit⁻¹ : ℤ_[2]ˣ) : ℤ_[2]))
          * gDelta h c (bridgeDress nu' j) := by
  have hA : chiSq h (bridgeDress nu' j) = 1 := gDelta_chiSq_bridgeDress nu' j
  have h1 : gDelta h c (commP (dsqSigma h) (bridgeDress nu' j))
      = (1 - ((SvalUnit⁻¹ : ℤ_[2]ˣ) : ℤ_[2])) * gDelta h c (bridgeDress nu' j) := by
    rw [gDelta_commP, hA, chiSq_sigma, inv_one]
    simp only [Units.val_one, sub_self, mul_zero, zero_mul, zero_add, one_mul]
  have h2 : gDelta h c (commP (bridgeDress nu' j) (dsqX0 h))
      = (((rootXUnit⁻¹ : ℤ_[2]ˣ) : ℤ_[2]) - 1) * gDelta h c (bridgeDress nu' j) := by
    rw [gDelta_commP, hA, chiSq_x0, inv_one]
    simp only [Units.val_one, sub_self, mul_zero, zero_mul, add_zero, one_mul]
  rw [gDeltaCoreLift, gDelta_mul, gDelta_mul, gDelta_eichLift_eq_zero, h1, h2]
  simp only [mul_zero, add_zero, gDelta_chiSq_commP, Units.val_one, one_mul]
  ring

/-- `X⁻¹ − S⁻¹ = 8 · unit`: the inverse difference inherits `v₂(S − X) = 3`. -/
theorem gDelta_inv_sub_inv :
    ∃ w : ℤ_[2]ˣ, ((rootXUnit⁻¹ : ℤ_[2]ˣ) : ℤ_[2]) - ((SvalUnit⁻¹ : ℤ_[2]ˣ) : ℤ_[2])
      = 2 ^ 3 * w := by
  obtain ⟨w, hw⟩ := gDelta_Sval_sub_rootX
  refine ⟨rootXUnit⁻¹ * SvalUnit⁻¹ * w, ?_⟩
  have hX : ((rootXUnit⁻¹ : ℤ_[2]ˣ) : ℤ_[2]) * rootX = 1 := by
    rw [← val_rootXUnit, ← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hS : ((SvalUnit⁻¹ : ℤ_[2]ˣ) : ℤ_[2]) * Sval = 1 := by
    rw [← val_SvalUnit, ← Units.val_mul, inv_mul_cancel, Units.val_one]
  rw [Units.val_mul, Units.val_mul]
  linear_combination
    (((rootXUnit⁻¹ : ℤ_[2]ˣ) : ℤ_[2]) * ((SvalUnit⁻¹ : ℤ_[2]ˣ) : ℤ_[2])) * hw
    + ((SvalUnit⁻¹ : ℤ_[2]ˣ) : ℤ_[2]) * hX
    - ((rootXUnit⁻¹ : ℤ_[2]ˣ) : ℤ_[2]) * hS

/-- ⭐⭐ **The layer-three reading of the core defect vanishes for every row**: every
lift of `cfourDefCore` has `2^3`-divisible value.  With
`cfourCmp_supply_of_core_vanish` in mind: the class-four residual carries no
component along any functional-protected direction. -/
theorem gDelta_dvd_of_levelMk_eq_defCore (c : Fin (sqRank h) → ℤ_[2])
    (nu' : ContinuousMonoidHom (DSq h : Type) (Multiplicative ℤ_[2])) (j : Fin h)
    {x : (DSq h : Type)}
    (hx : levelMk (DSq h : Type) 4 x = cfourDefCore nu' j) :
    (2 : ℤ_[2]) ^ 3 ∣ gDelta h c x := by
  have hlift : levelMk (DSq h : Type) 4 x
      = levelMk (DSq h : Type) 4 (gDeltaCoreLift nu' j) := by
    rw [hx, gDelta_coreLift_levelMk]
  refine gDelta_dvd_of_levelMk_eq c (k := 3) hlift ?_
  rw [gDelta_coreLift_eq]
  obtain ⟨w, hw⟩ := gDelta_inv_sub_inv
  rw [hw]
  exact (Dvd.intro _ rfl).mul_right _

/-- For rows in `2ℤ₂` (Labute's `2I`-normalization) the core defect's bound sharpens
to the full class-four precision `2^4`. -/
theorem gDelta_coreLift_dvd_of_even (c : Fin (sqRank h) → ℤ_[2])
    (hc : ∀ i, (2 : ℤ_[2]) ∣ c i)
    (nu' : ContinuousMonoidHom (DSq h : Type) (Multiplicative ℤ_[2])) (j : Fin h) :
    (2 : ℤ_[2]) ^ 4 ∣ gDelta h c (gDeltaCoreLift nu' j) := by
  rw [gDelta_coreLift_eq]
  obtain ⟨w, hw⟩ := gDelta_inv_sub_inv
  obtain ⟨t, ht⟩ := gDelta_two_dvd c hc (bridgeDress nu' j)
  rw [hw, ht]
  exact ⟨(w : ℤ_[2]) * t, by ring⟩

end CoreDefect

/-! ## §7 The honesty artifacts -/

section Honesty

variable {h : ℕ}

/-- **The untwisted reading**: any character `f` reads any relator value through the
abelianized row alone, `f(sqRelWord m) = (f(m 1)^4)⁻¹ · f(m 2)^2`.  Combined with the
bridge-row values this is why untwisted rows cannot kill the leftover (note §1.3):
the twist of §2 is not removable. -/
theorem gDelta_row_reading
    (f : ContinuousMonoidHom (DSq h : Type) (Multiplicative ℤ_[2]))
    (m : Fin (sqRank h) → (DSq h : Type)) :
    f (sqRelWord m) = (f (m 1) ^ 4)⁻¹ * f (m 2) ^ 2 := by
  rw [map_sqRelWord]
  exact sqRelWord_comm _

/-- The supply's `λ`-row clause pins the orientation only up to torsion:
`χ_sq(a)² = X^{2λ(a)} = 1` at a `λ`-trivial dressing slot. -/
theorem gDelta_chiSq_sq_of_nuLam {a : (DSq h : Type)} (hl : nuLam h a = 1) :
    (chiSq h a) ^ 2 = 1 := by
  rw [chiSq_sq_eq_lam, xPowLamSq_apply, hl]
  simp only [toAdd_one]
  rw [zpowZtwo, ofAdd_zero, map_one]

/-- ⭐ **The torsion gap** (recorded for W75): a `λ`-trivial dressing slot has
`χ_sq = ±1`.  The `+1` branch is covered by `GDeltaDefectVanishing`; the `−1` branch
evades the §5 master kill and is the exact gap between this lane's vanishing
statement and the supply's full dressing space. -/
theorem gDelta_chiSq_of_nuLam {a : (DSq h : Type)} (hl : nuLam h a = 1) :
    chiSq h a = 1 ∨ chiSq h a = -1 := by
  have hsq := gDelta_chiSq_sq_of_nuLam hl
  have hval : ((chiSq h a : ℤ_[2]ˣ) : ℤ_[2]) ^ 2 = 1 := by
    rw [← Units.val_pow_eq_pow_val, hsq, Units.val_one]
  have hfact : (((chiSq h a : ℤ_[2]ˣ) : ℤ_[2]) - 1)
      * (((chiSq h a : ℤ_[2]ˣ) : ℤ_[2]) + 1) = 0 := by
    linear_combination hval
  rcases mul_eq_zero.mp hfact with h1 | h1
  · left
    refine Units.ext ?_
    rw [Units.val_one]
    linear_combination h1
  · right
    refine Units.ext ?_
    rw [Units.val_neg, Units.val_one]
    linear_combination h1

end Honesty

/-! ## §8 Axiom pins -/

section AxiomPins

#print axioms gDeltaTop
#print axioms gDelta_continuous_equivProd
#print axioms gDelta_continuous_equivProd_symm
#print axioms gDelta_continuous_u
#print axioms gDelta_continuous_g
#print axioms gDeltaHomeo
#print axioms gDeltaTopGroup
#print axioms gDeltaCompact
#print axioms gDeltaT2
#print axioms gDeltaTotDisc
#print axioms gDelta_pow_u
#print axioms gDelta_two_pow_dvd_normSum
#print axioms gDelta_units_ball_subset
#print axioms gDelta_isProP
#print axioms gDeltaMark
#print axioms gDeltaMark_zero
#print axioms gDeltaMark_one
#print axioms gDeltaMark_two
#print axioms gDeltaMark_handleU
#print axioms gDeltaMark_handleV
#print axioms gDelta_datum
#print axioms gDelta_relWord_mark
#print axioms gDeltaHom
#print axioms gDeltaHom_gen
#print axioms gDelta
#print axioms gDelta_continuous
#print axioms gDelta_gen
#print axioms gDelta_chiSq_gen
#print axioms gDeltaBase
#print axioms gDeltaHom_g
#print axioms gDeltaHom_apply
#print axioms gDelta_one
#print axioms gDelta_mul
#print axioms gDelta_inv
#print axioms gDelta_pow
#print axioms gDelta_map_commP
#print axioms gDelta_commP
#print axioms gDelta_commutatorElement
#print axioms gDelta_commP_of_chi_one
#print axioms gDelta_isClosed_dvd_set
#print axioms gDelta_chi_sub_one_dvd
#print axioms gDelta_dvd_of_mem_twoCentral
#print axioms gDelta_two_dvd
#print axioms gDelta_dvd_of_levelMk_eq
#print axioms gDelta_sub_one_mul_normSum
#print axioms gDelta_normSum_unit
#print axioms gDelta_rootX_sub_one
#print axioms gDelta_Sval_sub_one
#print axioms gDelta_Sval_sub_rootX
#print axioms gDelta_sigma_tower
#print axioms gDelta_x0_tower
#print axioms gDelta_handleU_tower
#print axioms gDelta_not_two_dvd_unit
#print axioms gDelta_sigma_tower_notMem
#print axioms gDelta_x0_tower_notMem
#print axioms gDelta_handleU_tower_notMem
#print axioms gDelta_rootX_sq_add_one
#print axioms gDelta_Yval_sq_sub_one
#print axioms gDelta_x1_tower_dvd
#print axioms gDelta_chiSq_zpow_pivot
#print axioms gDelta_chiSq_zpow_handleU
#print axioms gDelta_chiSq_zpow_handleV
#print axioms gDelta_chiSq_sqEichU
#print axioms gDelta_chiSq_sqEichV
#print axioms gDelta_chiSq_bridgeDress
#print axioms gDelta_chiSq_bridgeTuple
#print axioms gDelta_chiFrame_arbBase
#print axioms gDelta_chiFrame_dressed
#print axioms gDelta_relWord_of_chiFrame
#print axioms gDelta_relWord_of_chiFrame_eq_zero
#print axioms gDelta_leftover_lift
#print axioms GDeltaDefectVanishing
#print axioms gDeltaDefectVanishing_holds
#print axioms gDelta_dvd_of_levelMk_eq_leftover
#print axioms gDeltaEichLift
#print axioms gDelta_eichLift_levelMk
#print axioms gDelta_eichLift_eq_zero
#print axioms gDelta_dvd_of_levelMk_eq_eichDefect
#print axioms gDeltaCoreLift
#print axioms gDelta_coreLift_levelMk
#print axioms gDelta_chiSq_commP
#print axioms gDelta_coreLift_eq
#print axioms gDelta_inv_sub_inv
#print axioms gDelta_dvd_of_levelMk_eq_defCore
#print axioms gDelta_coreLift_dvd_of_even
#print axioms gDelta_row_reading
#print axioms gDelta_chiSq_sq_of_nuLam
#print axioms gDelta_chiSq_of_nuLam

end AxiomPins

end SqCore

end Dyadic

end GQ2
