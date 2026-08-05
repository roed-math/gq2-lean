/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Fable-5
-/
import GQ2.Dyadic.Instances.GammaLSylowPreimageFieldLabuteLevelThreeSeed

/-!
# The odd-degree cup-adapted Frattini-frame supply

This file proves `GQ2.Dyadic.LSquare.OddDegreeSqCyclotomicFrattiniFrameSupply`: for every
finite `K/ℚ₂` of odd degree `n = 2h + 1` there is a `SqCyclotomicFrattiniFrame K h` whose
dual Frattini basis carries the field cup form to the constructor table of the improved
quadratic relator (`IsCupAdapted`).

## Strategy

Write `Q = G_K(2)`, `W = H¹(Q, 𝔽₂)` and let `b` be the field cup form transported through
degree-one inflation (`h1MaxProTwoEquivGalK`).  Three arithmetic classes control everything:

* `κ = cyclotomicModFourClassKTwo` — the mod-four cyclotomic sign, equal to the Kummer
  class `[-1]` (`CyclotomicKummerBridge`), hence the Bockstein/Labute vector of `b`
  (`b κ w = b w w`) with `b κ κ = 1` in odd degree;
* `τ = cyclotomicModEightOmegaClassKTwo` — Serre's `ω` row, equal to the Kummer class `[2]`
  (`CyclotomicKummerBridgeModEight`), orthogonal to `κ` and nonzero (odd-degree cyclotomic
  surjectivity realizes the value `X ≡ 5 (mod 8)`).

**Witt adaptation** (`frattiniFrameAdaptedModelEquiv`): the `⟨1⟩ ⊥ H^{⊥(h+1)}` normal form of
`Certificates/L.lean` is refined so that the `⟨1⟩` slot is `κ` (automatic: `κ` is the unique
vector representing the diagonal) and the first hyperbolic plane is spanned by a pair
`(ε₀, ε₁)` with `ε₀ + ε₁ = τ`.  Splitting off the plane on the pair `(w', w' + τ)` for any
`w'` with `b τ w' = 1` puts `τ` at coordinates `(1,1)`.

**Dualization** (`frattiniFrameEval_realizable`): evaluation of `1`-cocycles at group
elements identifies `Q` with the full linear dual of `W`: the image of evaluation is a
submodule of `Dual W`, and a functional vanishing on it would, by double duality
(`Module.evalEquiv`), come from a nonzero class all of whose cocycle values vanish.  The
generators are chosen as the dual family of the adapted coordinates.

**Exact cyclotomic values** (`frattiniFrameExactLift`): the dual family pins each generator's
Frattini coset, whose sharp mod-eight cyclotomic shadow is exactly the pair of values of
`κ` and `τ` on it.  The mod-16 congruences `S ≡ 13`, `X ≡ 5`, `Y ≡ 7` (`OrientationRoot`)
make those shadows match `(SvalUnit, rootXUnit, YvalUnit, 1, 1)` on the nose, so sharp exact
fibre lifting (`oddDegreeGalKSq_sharpExactLevelFibreLiftSupply`, from marked reciprocity)
replaces each representative by one with the exact `ℤ₂ˣ` value without moving its coset.

Frattini generation falls out of the same duality: a character killing all generators has all
adapted coordinates zero.

## Axioms

The main theorem prints std-3 together with the census axioms carried by its inputs:
`markedRecipAt` (B5-K, through cyclotomic surjectivity and sharp fibre lifting),
`tateDualityAt` (B6), `absGalQ2_localEulerCharacteristic` (B7) and
`hilbertSymbol_normCriterion_finiteDyadic` (B11a) through the cup normal form.  No new axiom,
no `sorry`, no `native_decide`.
-/

namespace GQ2.Dyadic.LSquare

noncomputable section

open GQ2 ContCoh
open GQ2.Roe.Labute
open GQ2.Dyadic.Certificates.LSqStokes
open scoped commutatorElement

local notation "ℚ̄₂" => AlgebraicClosure ℚ_[2]

namespace FrattiniFrameSupply

/-! ## §1 The coordinate model of the adapted normal form

`Model h` is `⟨1⟩ ⊥ H ⊥ H^{⊥h}` in explicit coordinates: the `𝔽₂` factor is the `⟨1⟩`
slot (frame index `2`), the middle plane carries frame indices `(0, 1)`, and the `j`-th
handle plane carries `(sqHandleIdxU j, sqHandleIdxV j)`. -/

/-- The coordinate model: `⟨1⟩`-slot × first hyperbolic plane × `h` handle planes. -/
abbrev Model (h : ℕ) : Type :=
  ZMod 2 × ((ZMod 2 × ZMod 2) × (Fin h → ZMod 2 × ZMod 2))

/-- The coordinate of a model vector at a core/handle position. -/
def modelCoordAt (h : ℕ) (s : Fin 3 ⊕ (Fin h × Fin 2)) (z : Model h) : ZMod 2 :=
  Sum.elim (fun a => if a = 0 then z.2.1.1 else if a = 1 then z.2.1.2 else z.1)
    (fun p => if p.2 = 0 then (z.2.2 p.1).1 else (z.2.2 p.1).2) s

theorem modelCoordAt_add (h : ℕ) (s : Fin 3 ⊕ (Fin h × Fin 2)) (z z' : Model h) :
    modelCoordAt h s (z + z') = modelCoordAt h s z + modelCoordAt h s z' := by
  rcases s with a | p
  · simp only [modelCoordAt, Sum.elim_inl]
    split_ifs <;> rfl
  · simp only [modelCoordAt, Sum.elim_inr]
    split_ifs <;> rfl

theorem modelCoordAt_zero (h : ℕ) (s : Fin 3 ⊕ (Fin h × Fin 2)) :
    modelCoordAt h s (0 : Model h) = 0 := by
  rcases s with a | p
  · simp only [modelCoordAt, Sum.elim_inl]
    split_ifs <;> rfl
  · simp only [modelCoordAt, Sum.elim_inr]
    split_ifs <;> rfl

theorem modelCoordAt_smul (h : ℕ) (s : Fin 3 ⊕ (Fin h × Fin 2)) (c : ZMod 2)
    (z : Model h) : modelCoordAt h s (c • z) = c * modelCoordAt h s z := by
  rcases ZMod.eq_zero_or_eq_one c with rfl | rfl
  · rw [zero_smul, modelCoordAt_zero, zero_mul]
  · rw [one_smul, one_mul]

/-- The coordinate at a core/handle position, as a linear functional. -/
def modelCoordL (h : ℕ) (s : Fin 3 ⊕ (Fin h × Fin 2)) :
    Model h →ₗ[ZMod 2] ZMod 2 where
  toFun := modelCoordAt h s
  map_add' := modelCoordAt_add h s
  map_smul' := modelCoordAt_smul h s

@[simp] theorem modelCoordL_apply (h : ℕ) (s : Fin 3 ⊕ (Fin h × Fin 2)) (z : Model h) :
    modelCoordL h s z = modelCoordAt h s z := rfl

@[simp] theorem modelCoordAt_inl_zero (h : ℕ) (z : Model h) :
    modelCoordAt h (Sum.inl 0) z = z.2.1.1 := by
  simp [modelCoordAt]

@[simp] theorem modelCoordAt_inl_one (h : ℕ) (z : Model h) :
    modelCoordAt h (Sum.inl 1) z = z.2.1.2 := by
  simp [modelCoordAt]

@[simp] theorem modelCoordAt_inl_two (h : ℕ) (z : Model h) :
    modelCoordAt h (Sum.inl 2) z = z.1 := by
  simp [modelCoordAt]

@[simp] theorem modelCoordAt_inr_zero (h : ℕ) (j : Fin h) (z : Model h) :
    modelCoordAt h (Sum.inr (j, 0)) z = (z.2.2 j).1 := by
  simp [modelCoordAt]

@[simp] theorem modelCoordAt_inr_one (h : ℕ) (j : Fin h) (z : Model h) :
    modelCoordAt h (Sum.inr (j, 1)) z = (z.2.2 j).2 := by
  simp [modelCoordAt]

/-- A model vector with all core/handle coordinates zero is zero. -/
theorem modelCoordAt_eq_zero (h : ℕ) (z : Model h)
    (hall : ∀ s, modelCoordAt h s z = 0) : z = 0 := by
  refine Prod.ext ?_ (Prod.ext (Prod.ext ?_ ?_) (funext fun j => Prod.ext ?_ ?_))
  · exact (modelCoordAt_inl_two h z).symm.trans (hall (Sum.inl 2))
  · exact (modelCoordAt_inl_zero h z).symm.trans (hall (Sum.inl 0))
  · exact (modelCoordAt_inl_one h z).symm.trans (hall (Sum.inl 1))
  · exact (modelCoordAt_inr_zero h j z).symm.trans (hall (Sum.inr (j, 0)))
  · exact (modelCoordAt_inr_one h j z).symm.trans (hall (Sum.inr (j, 1)))

/-- The model Gram form `⟨1⟩ ⊥ H ⊥ H^{⊥h}`. -/
def modelGram (h : ℕ) (z z' : Model h) : ZMod 2 :=
  z.1 * z'.1 + (z.2.1.1 * z'.2.1.2 + z.2.1.2 * z'.2.1.1) + hypGram z.2.2 z'.2.2

/-- The model Gram is the improved-relator constructor table in model coordinates. -/
theorem sqRelatorQuadraticInitialGram_modelCoord (h : ℕ) (z z' : Model h) :
    GQ2.ContCoh.sqRelatorQuadraticInitialGram h
        (fun i j => modelCoordAt h (GQ2.ContCoh.sqInitialAlphabetEquiv h i) z *
          modelCoordAt h (GQ2.ContCoh.sqInitialAlphabetEquiv h j) z') =
      modelGram h z z' := by
  rw [GQ2.ContCoh.sqRelatorQuadraticInitialGram, modelGram]
  simp only [GQ2.ContCoh.sqInitialAlphabetEquiv_zero, GQ2.ContCoh.sqInitialAlphabetEquiv_one,
    GQ2.ContCoh.sqInitialAlphabetEquiv_two, GQ2.ContCoh.sqInitialAlphabetEquiv_handleU,
    GQ2.ContCoh.sqInitialAlphabetEquiv_handleV, modelCoordAt_inl_zero, modelCoordAt_inl_one,
    modelCoordAt_inl_two, modelCoordAt_inr_zero, modelCoordAt_inr_one]
  rw [hypGram]

/-! ## §2 The Witt adaptation

Any nondegenerate cup–Bockstein form with anisotropic Labute vector `e` and a second vector
`t ≠ 0` orthogonal to `e` admits an isometry to the model in which `e ↦ (1, 0)` and
`t ↦ (0, ((1,1), 0))`. -/

section Adapted

variable {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]

/-- **The adapted normal form.**  Refines `exists_cupForm_normalForm`: the `⟨1⟩` slot is the
Labute vector `e` itself, and the auxiliary vector `t` (orthogonal to `e`, nonzero) spans the
diagonal `(1,1)` of the first hyperbolic plane. -/
theorem frattiniFrameAdaptedModelEquiv [Finite W] {b : W → W → ZMod 2}
    (hb : IsCupFormFp2 b) (hnd : NondegFp2 b) {e t : W}
    (he : ∀ w, b e w = b w w) (he1 : b e e = 1) (hte : b t e = 0) (htne : t ≠ 0)
    {h : ℕ} (hcard : Nat.card W = 2 ^ (2 * h + 3)) :
    ∃ Φ : W ≃ₗ[ZMod 2] Model h,
      (∀ x y, b x y = modelGram h (Φ x) (Φ y)) ∧
        Φ e = (1, 0) ∧ Φ t = (0, ((1, 1), 0)) := by
  classical
  have h2W : ∀ x : W, x + x = 0 := GQ2.Dyadic.Certificates.module_zmod2_two_torsion
  -- `t` lies in the diagonal kernel
  have htt : b t t = 0 := by rw [← he t, hb.symm]; exact hte
  set tK : cupKer hb := ⟨t, htt⟩ with htK
  have htKne : tK ≠ 0 := by
    intro hzero
    exact htne (congrArg Subtype.val hzero)
  -- the symplectic structure on the diagonal kernel
  have hbK := isSymplectic_cupKer hb hnd he he1
  -- a hyperbolic partner for `t`
  have hex : ∃ w' : cupKer hb, b (tK : W) (w' : W) = 1 := by
    by_contra hcon
    push Not at hcon
    refine htKne (hbK.nondeg tK fun y => ?_)
    rcases ZMod.eq_zero_or_eq_one (b (tK : W) (y : W)) with h0 | h1
    · exact h0
    · exact absurd h1 (hcon y)
  obtain ⟨w', hw'⟩ := hex
  have hw't : b (w' : W) t = 1 := by rw [hb.symm]; exact hw'
  -- split along the pair `(v, w) = (w', w' + t)`, which sees `t` at coordinates `(1, 1)`
  set v : cupKer hb := w' with hv
  set w : cupKer hb := w' + tK with hw
  have hvw : b (v : W) (w : W) = 1 := by
    have : b (w' : W) ((w' : W) + t) = 1 := by
      rw [hb.add_right, hw't]
      have : b (w' : W) (w' : W) = 0 := w'.2
      rw [this, zero_add]
    exact this
  set e1 := hypSplitEquiv hbK hvw with he1def
  have hPsymp := isSymplectic_restrict hbK hvw
  -- finite instances
  haveI : Finite (cupKer hb) := Subtype.finite
  haveI : Finite (hypPerp (fun x y : cupKer hb => b (x : W) (y : W)) hbK v w) :=
    Subtype.finite
  obtain ⟨m, φ', hφ'⟩ := exists_symplectic_equiv _ hPsymp
  -- pin `m = h` by cardinality
  have hm : m = h := by
    have hc1 : Nat.card W = 2 * Nat.card (cupKer hb) := by
      rw [Nat.card_congr (cupSplitEquiv hb he he1).toEquiv, Nat.card_prod]
      simp
    have hc2 : Nat.card (cupKer hb) = 4 *
        Nat.card (hypPerp (fun x y : cupKer hb => b (x : W) (y : W)) hbK v w) := by
      rw [Nat.card_congr e1.toEquiv, Nat.card_prod]
      simp
    have hc3 : Nat.card
        (hypPerp (fun x y : cupKer hb => b (x : W) (y : W)) hbK v w) = 4 ^ m := by
      rw [Nat.card_congr φ'.toEquiv]
      simp
    have hchain : (2 : ℕ) ^ (2 * m + 3) = 2 ^ (2 * h + 3) := by
      rw [← hcard, hc1, hc2, hc3, show (4 : ℕ) = 2 ^ 2 from rfl, ← pow_mul]
      ring
    have := Nat.pow_right_injective (le_refl 2) hchain
    omega
  have hm' : h = m := hm.symm
  subst hm'
  -- assemble the equivalence
  set φ₀ := cupSplitEquiv hb he he1 with hφ₀
  set Φ : W ≃ₗ[ZMod 2] Model h := φ₀.trans ((LinearEquiv.refl (ZMod 2) (ZMod 2)).prodCongr
    (e1.trans ((LinearEquiv.refl (ZMod 2) (ZMod 2 × ZMod 2)).prodCongr φ'))) with hΦ
  have hΦapp : ∀ u : W, Φ u = ((φ₀ u).1, ((e1 (φ₀ u).2).1, φ' (e1 (φ₀ u).2).2)) := by
    intro u
    rw [hΦ]
    simp only [LinearEquiv.trans_apply, LinearEquiv.prodCongr_apply, LinearEquiv.refl_apply]
  -- the split Gram, read through `e1` and `φ'`
  have hsplit2 : ∀ k k' : cupKer hb, b (k : W) (k' : W) =
      ((e1 k).1.1 * (e1 k').1.2 + (e1 k).1.2 * (e1 k').1.1) +
        hypGram (φ' (e1 k).2) (φ' (e1 k').2) := by
    intro k k'
    have h1 := hypSplit_gram hbK hvw k k'
    have h2 := hφ' (e1 k).2 (e1 k').2
    refine h1.trans ?_
    rw [← h2]
    rfl
  refine ⟨Φ, ?_, ?_, ?_⟩
  · -- the Gram identity
    intro x y
    have hx : (φ₀ x).1 • e + ((φ₀ x).2 : W) = x := φ₀.left_inv x
    have hy : (φ₀ y).1 • e + ((φ₀ y).2 : W) = y := φ₀.left_inv y
    have hsplit : b x y = (φ₀ x).1 * (φ₀ y).1 + b ((φ₀ x).2 : W) ((φ₀ y).2 : W) := by
      calc b x y = b ((φ₀ x).1 • e + ((φ₀ x).2 : W)) ((φ₀ y).1 • e + ((φ₀ y).2 : W)) := by
            rw [hx, hy]
        _ = (φ₀ x).1 * (φ₀ y).1 + b ((φ₀ x).2 : W) ((φ₀ y).2 : W) :=
            cupSplit_gram hb he he1 _ _ _ _
    rw [hΦapp x, hΦapp y]
    show b x y = (φ₀ x).1 * (φ₀ y).1 +
      ((e1 (φ₀ x).2).1.1 * (e1 (φ₀ y).2).1.2 + (e1 (φ₀ x).2).1.2 * (e1 (φ₀ y).2).1.1) +
        hypGram (φ' (e1 (φ₀ x).2).2) (φ' (e1 (φ₀ y).2).2)
    rw [hsplit, hsplit2 (φ₀ x).2 (φ₀ y).2]
    ring
  · -- the Labute vector sits in the `⟨1⟩` slot
    have h0 : φ₀ e = (1, 0) := by
      refine Prod.ext he1 (Subtype.ext ?_)
      show e + (b e e) • e = 0
      rw [he1, one_smul, h2W]
    rw [hΦapp e, h0]
    simp
  · -- the `ω`-vector spans the diagonal of the first plane
    have h0 : φ₀ t = (0, tK) := by
      have hbet : b e t = 0 := by rw [hb.symm]; exact hte
      refine Prod.ext hbet (Subtype.ext ?_)
      show t + (b e t) • e = t
      rw [hbet, zero_smul, add_zero]
    have h1 : e1 tK = ((1, 1), 0) := by
      have hwtK : b (w : W) (tK : W) = 1 := by
        show b ((w' : W) + t) t = 1
        rw [hb.add_left, hw't, htt, add_zero]
      have hvtK : b (v : W) (tK : W) = 1 := hw't
      refine Prod.ext (Prod.ext ?_ ?_) (Subtype.ext ?_)
      · exact hwtK
      · exact hvtK
      · show tK + (b (w : W) (tK : W)) • v + (b (v : W) (tK : W)) • w = 0
        rw [hwtK, hvtK, one_smul, one_smul]
        show tK + w' + (w' + tK) = 0
        have hh : tK + w' + (w' + tK) = (tK + tK) + (w' + w') := by abel
        rw [hh, GQ2.Dyadic.Certificates.module_zmod2_two_torsion,
          GQ2.Dyadic.Certificates.module_zmod2_two_torsion, add_zero]
    rw [hΦapp t, h0, h1]
    simp

end Adapted

/-! ## §3 Mod-two characters of a finite elementary-abelian level quotient -/

section Elementary

/-- The level-two quotient is commutative (commutators die in `λ₂`). -/
theorem frattiniFrame_levelTwo_mul_comm (G : Type) [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] (a b : GQ2.Roe.Labute.levelQuot G 2) : a * b = b * a := by
  obtain ⟨g, rfl⟩ := GQ2.Roe.Labute.levelMk_surjective G 2 a
  obtain ⟨g', rfl⟩ := GQ2.Roe.Labute.levelMk_surjective G 2 b
  rw [← map_mul, ← map_mul]
  have hmem : (g * g')⁻¹ * (g' * g) ∈ GQ2.Roe.Labute.twoCentralSeries G 2 := by
    have hword : (g * g')⁻¹ * (g' * g) = ⁅g'⁻¹, g⁻¹⁆ := by
      rw [commutatorElement_def]
      group
    rw [hword]
    have h1 : g'⁻¹ ∈ GQ2.Roe.Labute.twoCentralSeries G 1 := by
      rw [GQ2.Roe.Labute.twoCentralSeries_one]
      exact Subgroup.mem_top _
    exact GQ2.Roe.Labute.commutator_mem_twoCentralSeries_succ G h1 _
  exact (QuotientGroup.eq (s := GQ2.Roe.Labute.twoCentralSeries G 2)).mpr hmem

/-- The level-two quotient is elementary (squares die in `λ₂`). -/
theorem frattiniFrame_levelTwo_sq (G : Type) [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] (a : GQ2.Roe.Labute.levelQuot G 2) : a * a = 1 := by
  obtain ⟨g, rfl⟩ := GQ2.Roe.Labute.levelMk_surjective G 2 a
  rw [← map_mul, ← pow_two]
  have h1 : g ∈ GQ2.Roe.Labute.twoCentralSeries G 1 := by
    rw [GQ2.Roe.Labute.twoCentralSeries_one]
    exact Subgroup.mem_top _
  exact (QuotientGroup.eq_one_iff _).mpr
    (GQ2.Roe.Labute.sq_mem_twoCentralSeries_succ G h1)

/-- A proper subgroup of a finite elementary abelian `2`-group is killed by a nontrivial
mod-two character.  (Linear duality for the associated `𝔽₂`-space.) -/
theorem frattiniFrame_exists_modTwo_character {F : Type} [Group F] [Finite F]
    (hcomm : ∀ a b : F, a * b = b * a) (hsq : ∀ a : F, a * a = 1)
    {H : Subgroup F} (hne : H ≠ ⊤) :
    ∃ c : F →* Multiplicative (ZMod 2), (∀ x, x ∈ H → c x = 1) ∧ c ≠ 1 := by
  classical
  letI : CommGroup F := { (inferInstance : Group F) with mul_comm := hcomm }
  letI : Module (ZMod 2) (Additive F) := AddCommGroup.zmodModule (by
    intro x
    rw [two_nsmul]
    exact hsq x.toMul)
  haveI : Finite (Additive F) := Finite.of_equiv F Additive.ofMul
  -- the subgroup as an `𝔽₂`-subspace
  let p : Submodule (ZMod 2) (Additive F) :=
    { carrier := {x | x.toMul ∈ H}
      add_mem' := fun hx hy => H.mul_mem hx hy
      zero_mem' := H.one_mem
      smul_mem' := by
        intro c x hx
        rcases ZMod.eq_zero_or_eq_one c with rfl | rfl
        · rw [zero_smul]; exact H.one_mem
        · rw [one_smul]; exact hx }
  have hp : p ≠ ⊤ := by
    intro htop
    apply hne
    rw [Subgroup.eq_top_iff']
    intro x
    have hx : Additive.ofMul x ∈ p := by
      rw [htop]
      exact Submodule.mem_top
    exact hx
  obtain ⟨a, ha⟩ : ∃ a : Additive F, a ∉ p := by
    by_contra hall
    push Not at hall
    exact hp (Submodule.eq_top_iff'.mpr hall)
  have haq : (Submodule.Quotient.mk a : Additive F ⧸ p) ≠ 0 := by
    rw [Ne, Submodule.Quotient.mk_eq_zero]
    exact ha
  obtain ⟨φ, hφ⟩ : ∃ φ : Module.Dual (ZMod 2) (Additive F ⧸ p),
      φ (Submodule.Quotient.mk a) ≠ 0 := by
    by_contra hall
    push Not at hall
    exact haq ((Module.forall_dual_apply_eq_zero_iff (ZMod 2) _).mp hall)
  refine ⟨{ toFun := fun x => Multiplicative.ofAdd (φ (Submodule.Quotient.mk (Additive.ofMul x)))
            map_one' := by
              show Multiplicative.ofAdd (φ (Submodule.Quotient.mk (0 : Additive F))) = 1
              rw [Submodule.Quotient.mk_zero, map_zero]
              rfl
            map_mul' := by
              intro x y
              show Multiplicative.ofAdd
                  (φ (Submodule.Quotient.mk (Additive.ofMul x + Additive.ofMul y))) = _
              rw [Submodule.Quotient.mk_add, map_add]
              rfl }, ?_, ?_⟩
  · intro x hx
    show Multiplicative.ofAdd (φ (Submodule.Quotient.mk (Additive.ofMul x))) = 1
    rw [(Submodule.Quotient.mk_eq_zero p).mpr (show Additive.ofMul x ∈ p from hx), map_zero]
    rfl
  · intro hone
    apply hφ
    have := DFunLike.congr_fun hone (Additive.toMul a)
    simpa using this

end Elementary

/-! ## §4 The evaluation pairing on `H¹(G_K(2), 𝔽₂)`

Evaluation of the trivial-action `1`-cocycle representative at a group element.  This is
biadditive, factors through the level-two (Frattini) quotient, computes `characterClass`
values definitionally, and realizes every linear functional (finite double duality). -/

section Eval

variable {K : IntermediateField ℚ_[2] ℚ̄₂}
  [CompactSpace (GalK K)] [TotallyDisconnectedSpace (GalK K)]

local instance : DistribMulAction (maxProPQuotient 2 (GalK K)) (ZMod 2) :=
  scalarActionZmodTwo _

local instance : ContinuousSMul (maxProPQuotient 2 (GalK K)) (ZMod 2) :=
  scalarActionZmodTwo_continuousSMul _

/-- Evaluation of a degree-one class of `G_K(2)` at a group element (trivial action, so the
cocycle representative is unique). -/
def frattiniFrameEval (x : H1 (maxProPQuotient 2 (GalK K)) (ZMod 2))
    (g : maxProPQuotient 2 (GalK K)) : ZMod 2 :=
  ((H1equivZ1OfTrivial (fun _ _ => rfl)) x).1 g

/-- On character classes, evaluation is evaluation. -/
theorem frattiniFrameEval_characterClass
    (c : ContinuousMonoidHom (maxProPQuotient 2 (GalK K)) (Multiplicative (ZMod 2)))
    (g : maxProPQuotient 2 (GalK K)) :
    frattiniFrameEval (SqCyclotomicFrattiniFrame.characterClass (K := K) c) g =
      Multiplicative.toAdd (c g) := rfl

theorem frattiniFrameEval_add (x y : H1 (maxProPQuotient 2 (GalK K)) (ZMod 2))
    (g : maxProPQuotient 2 (GalK K)) :
    frattiniFrameEval (x + y) g = frattiniFrameEval x g + frattiniFrameEval y g := by
  unfold frattiniFrameEval
  rw [map_add]
  rfl

theorem frattiniFrameEval_zero (g : maxProPQuotient 2 (GalK K)) :
    frattiniFrameEval (0 : H1 (maxProPQuotient 2 (GalK K)) (ZMod 2)) g = 0 := by
  unfold frattiniFrameEval
  rw [map_zero]
  rfl

theorem frattiniFrameEval_smul (c : ZMod 2)
    (x : H1 (maxProPQuotient 2 (GalK K)) (ZMod 2)) (g : maxProPQuotient 2 (GalK K)) :
    frattiniFrameEval (c • x) g = c * frattiniFrameEval x g := by
  rcases ZMod.eq_zero_or_eq_one c with rfl | rfl
  · rw [zero_smul, frattiniFrameEval_zero, zero_mul]
  · rw [one_smul, one_mul]

theorem frattiniFrameEval_mul (x : H1 (maxProPQuotient 2 (GalK K)) (ZMod 2))
    (g g' : maxProPQuotient 2 (GalK K)) :
    frattiniFrameEval x (g * g') = frattiniFrameEval x g + frattiniFrameEval x g' :=
  ((mem_Z1_iff_of_trivial (fun _ _ => rfl)).mp
    ((H1equivZ1OfTrivial (fun _ _ => rfl)) x).2).2 g g'

theorem frattiniFrameEval_one (x : H1 (maxProPQuotient 2 (GalK K)) (ZMod 2)) :
    frattiniFrameEval x (1 : maxProPQuotient 2 (GalK K)) = 0 :=
  Z1_apply_one _

/-- A class with all evaluations zero is zero. -/
theorem frattiniFrameEval_eq_zero (x : H1 (maxProPQuotient 2 (GalK K)) (ZMod 2))
    (hall : ∀ g, frattiniFrameEval x g = 0) : x = 0 := by
  apply (H1equivZ1OfTrivial (fun _ _ => rfl)).injective
  rw [map_zero]
  exact Subtype.ext (funext hall)

/-- Evaluation only depends on the level-two (Frattini) coset. -/
theorem frattiniFrameEval_eq_of_levelMk_eq (x : H1 (maxProPQuotient 2 (GalK K)) (ZMod 2))
    {g g' : maxProPQuotient 2 (GalK K)}
    (hlevel : levelMk (maxProPQuotient 2 (GalK K)) 2 g =
      levelMk (maxProPQuotient 2 (GalK K)) 2 g') :
    frattiniFrameEval x g = frattiniFrameEval x g' := by
  have hmem : g⁻¹ * g' ∈ twoCentralSeries (maxProPQuotient 2 (GalK K)) 2 :=
    (QuotientGroup.eq_one_iff _).mp (by
      show levelMk (maxProPQuotient 2 (GalK K)) 2 (g⁻¹ * g') = 1
      rw [map_mul, map_inv, hlevel, inv_mul_cancel])
  set z := (H1equivZ1OfTrivial (fun _ _ => rfl)) x with hz
  set c : ContinuousMonoidHom (maxProPQuotient 2 (GalK K)) (Multiplicative (ZMod 2)) :=
    Count.homEquivZ1.symm z with hc
  have hcz : ∀ y, frattiniFrameEval x y = Multiplicative.toAdd (c y) := by
    intro y
    show z.1 y = _
    conv_lhs => rw [← Count.homEquivZ1.apply_symm_apply z]
    rfl
  have hker : c (g⁻¹ * g') = 1 :=
    MonoidHom.mem_ker.mp (twoCentralSeries_two_le_continuousCharacter_ker c hmem)
  rw [hcz g, hcz g', show g' = g * (g⁻¹ * g') from by group, map_mul, hker, mul_one]

/-- Evaluation at a fixed element, as a linear functional on `H¹`. -/
def frattiniFrameEvalL (g : maxProPQuotient 2 (GalK K)) :
    Module.Dual (ZMod 2) (H1 (maxProPQuotient 2 (GalK K)) (ZMod 2)) where
  toFun x := frattiniFrameEval x g
  map_add' x y := frattiniFrameEval_add x y g
  map_smul' c x := frattiniFrameEval_smul c x g

@[simp] theorem frattiniFrameEvalL_apply (g : maxProPQuotient 2 (GalK K))
    (x : H1 (maxProPQuotient 2 (GalK K)) (ZMod 2)) :
    frattiniFrameEvalL (K := K) g x = frattiniFrameEval x g := rfl

/-- **Evaluation realizes every linear functional** on `H¹(G_K(2), 𝔽₂)`: the image of
`frattiniFrameEvalL` is a submodule of the dual, and by finite double duality a functional
killing it would come from a nonzero class with identically vanishing cocycle. -/
theorem frattiniFrameEval_realizable
    (hfin : Finite (H1 (maxProPQuotient 2 (GalK K)) (ZMod 2)))
    (φ : Module.Dual (ZMod 2) (H1 (maxProPQuotient 2 (GalK K)) (ZMod 2))) :
    ∃ g : maxProPQuotient 2 (GalK K), ∀ x, frattiniFrameEval x g = φ x := by
  classical
  haveI := hfin
  set S : Submodule (ZMod 2)
      (Module.Dual (ZMod 2) (H1 (maxProPQuotient 2 (GalK K)) (ZMod 2))) :=
    { carrier := Set.range (frattiniFrameEvalL (K := K))
      add_mem' := by
        rintro ψ χ ⟨g, rfl⟩ ⟨g', rfl⟩
        refine ⟨g * g', ?_⟩
        ext x
        exact frattiniFrameEval_mul x g g'
      zero_mem' := by
        refine ⟨1, ?_⟩
        ext x
        exact frattiniFrameEval_one x
      smul_mem' := by
        intro c ψ hψ
        rcases ZMod.eq_zero_or_eq_one c with rfl | rfl
        · rw [zero_smul]
          refine ⟨1, ?_⟩
          ext x
          exact frattiniFrameEval_one x
        · rw [one_smul]
          exact hψ } with hSdef
  suffices hStop : S = ⊤ by
    have hφS : φ ∈ S := by
      rw [hStop]
      exact Submodule.mem_top
    obtain ⟨g, hg⟩ := hφS
    exact ⟨g, fun x => (DFunLike.congr_fun hg x :)⟩
  by_contra hne
  obtain ⟨ψ₀, hψ₀⟩ : ∃ ψ₀, ψ₀ ∉ S := by
    by_contra hall
    push Not at hall
    exact hne (Submodule.eq_top_iff'.mpr hall)
  have hq0 : S.mkQ ψ₀ ≠ 0 := by
    rw [Submodule.mkQ_apply, Ne, Submodule.Quotient.mk_eq_zero]
    exact hψ₀
  obtain ⟨Ξ', hΞ'⟩ : ∃ Ξ' : Module.Dual (ZMod 2)
      ((Module.Dual (ZMod 2) (H1 (maxProPQuotient 2 (GalK K)) (ZMod 2))) ⧸ S),
      Ξ' (S.mkQ ψ₀) ≠ 0 := by
    by_contra hall
    push Not at hall
    exact hq0 ((Module.forall_dual_apply_eq_zero_iff (ZMod 2) _).mp hall)
  set Ξ := Ξ'.comp S.mkQ with hΞ
  set w₀ := (Module.evalEquiv (ZMod 2)
    (H1 (maxProPQuotient 2 (GalK K)) (ZMod 2))).symm Ξ with hw₀def
  have hw₀ : ∀ ψ : Module.Dual (ZMod 2) (H1 (maxProPQuotient 2 (GalK K)) (ZMod 2)),
      ψ w₀ = Ξ ψ := fun ψ => Module.apply_evalEquiv_symm_apply (ZMod 2) _ ψ Ξ
  have hker : ∀ g : maxProPQuotient 2 (GalK K), frattiniFrameEval w₀ g = 0 := by
    intro g
    have hmem : frattiniFrameEvalL (K := K) g ∈ S := ⟨g, rfl⟩
    have hval : Ξ (frattiniFrameEvalL (K := K) g) = 0 := by
      rw [hΞ]
      show Ξ' (S.mkQ (frattiniFrameEvalL (K := K) g)) = 0
      rw [Submodule.mkQ_apply, (Submodule.Quotient.mk_eq_zero S).mpr hmem, map_zero]
    calc frattiniFrameEval w₀ g = frattiniFrameEvalL (K := K) g w₀ := rfl
      _ = Ξ (frattiniFrameEvalL (K := K) g) := hw₀ _
      _ = 0 := hval
  have hw₀0 : w₀ = 0 := frattiniFrameEval_eq_zero w₀ hker
  apply hΞ'
  have hΞψ₀ : Ξ ψ₀ = 0 := by
    rw [← hw₀ ψ₀, hw₀0, map_zero]
  rw [hΞ] at hΞψ₀
  exact hΞψ₀

end Eval

/-! ## §5 Mod-eight unit data and the exact-value computations -/

section UnitData

open GQ2.HilbertSymbol

/-- The two mod-two components of a mod-eight unit: mod-four parity and Serre's `ω`.
Together they determine the unit. -/
def unitsModEightData (u : (ZMod 8)ˣ) : ZMod 2 × ZMod 2 :=
  (Multiplicative.toAdd (unitsModFourParity
      (Units.map (ZMod.castHom (by norm_num : (4 : ℕ) ∣ 8) (ZMod 4)).toMonoidHom u)),
    Multiplicative.toAdd (unitsModEightOmega u))

theorem unitsModEightData_injective : Function.Injective unitsModEightData := by decide

/-- Casting the mod-eight reduction of a `2`-adic unit to `ZMod 4` is the mod-four
reduction. -/
theorem frattiniFrame_unitsMap_cast (u : ℤ_[2]ˣ) :
    Units.map (ZMod.castHom (by norm_num : (4 : ℕ) ∣ 8) (ZMod 4)).toMonoidHom
        (Units.map (PadicInt.toZModPow 3).toMonoidHom u) =
      Units.map (PadicInt.toZModPow 2).toMonoidHom u := by
  apply Units.ext
  show ZMod.castHom (by norm_num : (4 : ℕ) ∣ 8) (ZMod 4)
      (PadicInt.toZModPow 3 ((u : ℤ_[2]ˣ) : ℤ_[2])) = PadicInt.toZModPow 2 ((u : ℤ_[2]ˣ) : ℤ_[2])
  rw [ZMod.castHom_apply, PadicInt.cast_toZModPow 2 3 (by norm_num)]

/-- Parity of a mod-four unit with residue `1`. -/
theorem frattiniFrame_parity_of_val_one {u : (ZMod 4)ˣ} (hval : (u : ZMod 4) = 1) :
    Multiplicative.toAdd (unitsModFourParity u) = 0 := by
  have hu : u = 1 := Units.ext (by rw [hval, Units.val_one])
  rw [hu, map_one, toAdd_one]

/-- Parity of a mod-four unit with residue `3`. -/
theorem frattiniFrame_parity_of_val_three {u : (ZMod 4)ˣ} (hval : (u : ZMod 4) = 3) :
    Multiplicative.toAdd (unitsModFourParity u) = 1 := by
  have hne : u ≠ 1 := by
    intro h1
    rw [h1, Units.val_one] at hval
    exact absurd hval (by decide)
  show Multiplicative.toAdd (if u = 1 then 1 else Multiplicative.ofAdd 1) = 1
  rw [if_neg hne]
  rfl

/-- `ω` of a mod-eight unit through its residue. -/
theorem frattiniFrame_omega_of_val {u : (ZMod 8)ˣ} {r : ZMod 8} (hval : (u : ZMod 8) = r) :
    Multiplicative.toAdd (unitsModEightOmega u) = omegaResidue r := by
  show omegaResidue ((u : ZMod 8)) = omegaResidue r
  rw [hval]

/-- `S ≡ 1 (mod 4)` (from `S ≡ 13 (mod 16)`). -/
theorem frattiniFrame_Sval_modFour :
    PadicInt.toZModPow 2 ((GQ2.Roe.SvalUnit : ℤ_[2]ˣ) : ℤ_[2]) = 1 := by
  rw [GQ2.Roe.val_SvalUnit, ← PadicInt.cast_toZModPow 2 4 (by norm_num),
    GQ2.Roe.Sval_toZModPow_four]
  decide

/-- `S ≡ 5 (mod 8)` (from `S ≡ 13 (mod 16)`). -/
theorem frattiniFrame_Sval_modEight :
    PadicInt.toZModPow 3 ((GQ2.Roe.SvalUnit : ℤ_[2]ˣ) : ℤ_[2]) = 5 := by
  rw [GQ2.Roe.val_SvalUnit, ← PadicInt.cast_toZModPow 3 4 (by norm_num),
    GQ2.Roe.Sval_toZModPow_four]
  decide

/-- `X ≡ 1 (mod 4)` (from `X ≡ 5 (mod 16)`). -/
theorem frattiniFrame_rootX_modFour :
    PadicInt.toZModPow 2 ((GQ2.Roe.rootXUnit : ℤ_[2]ˣ) : ℤ_[2]) = 1 := by
  rw [GQ2.Roe.val_rootXUnit, ← PadicInt.cast_toZModPow 2 4 (by norm_num),
    GQ2.Roe.rootX_toZModPow_four]
  decide

/-- `X ≡ 5 (mod 8)` (from `X ≡ 5 (mod 16)`). -/
theorem frattiniFrame_rootX_modEight :
    PadicInt.toZModPow 3 ((GQ2.Roe.rootXUnit : ℤ_[2]ˣ) : ℤ_[2]) = 5 := by
  rw [GQ2.Roe.val_rootXUnit, ← PadicInt.cast_toZModPow 3 4 (by norm_num),
    GQ2.Roe.rootX_toZModPow_four]
  decide

/-- `Y ≡ 3 (mod 4)` (from `Y ≡ 7 (mod 16)`). -/
theorem frattiniFrame_Yval_modFour :
    PadicInt.toZModPow 2 ((GQ2.Roe.YvalUnit : ℤ_[2]ˣ) : ℤ_[2]) = 3 := by
  rw [GQ2.Roe.val_YvalUnit, ← PadicInt.cast_toZModPow 2 4 (by norm_num),
    GQ2.Roe.Yval_toZModPow_four]
  decide

/-- `Y ≡ 7 (mod 8)` (from `Y ≡ 7 (mod 16)`). -/
theorem frattiniFrame_Yval_modEight :
    PadicInt.toZModPow 3 ((GQ2.Roe.YvalUnit : ℤ_[2]ˣ) : ℤ_[2]) = 7 := by
  rw [GQ2.Roe.val_YvalUnit, ← PadicInt.cast_toZModPow 3 4 (by norm_num),
    GQ2.Roe.Yval_toZModPow_four]
  decide

/-- The improved-frame cyclotomic value table: `S, X, Y` on the three core indices, `1` on
every handle index. -/
def frattiniFrameTarget (h : ℕ) (i : Fin (SqCore.sqRank h)) : ℤ_[2]ˣ :=
  Sum.elim (fun a : Fin 3 =>
      if a = 0 then GQ2.Roe.SvalUnit else if a = 1 then GQ2.Roe.rootXUnit
      else GQ2.Roe.YvalUnit)
    (fun _ => 1) (GQ2.ContCoh.sqInitialAlphabetEquiv h i)

@[simp] theorem frattiniFrameTarget_zero (h : ℕ) :
    frattiniFrameTarget h 0 = GQ2.Roe.SvalUnit := by
  unfold frattiniFrameTarget
  rw [GQ2.ContCoh.sqInitialAlphabetEquiv_zero]
  simp

@[simp] theorem frattiniFrameTarget_one (h : ℕ) :
    frattiniFrameTarget h 1 = GQ2.Roe.rootXUnit := by
  unfold frattiniFrameTarget
  rw [GQ2.ContCoh.sqInitialAlphabetEquiv_one]
  simp

@[simp] theorem frattiniFrameTarget_two (h : ℕ) :
    frattiniFrameTarget h 2 = GQ2.Roe.YvalUnit := by
  unfold frattiniFrameTarget
  rw [GQ2.ContCoh.sqInitialAlphabetEquiv_two]
  simp

@[simp] theorem frattiniFrameTarget_handleU {h : ℕ} (j : Fin h) :
    frattiniFrameTarget h (SqCore.sqHandleIdxU j) = 1 := by
  unfold frattiniFrameTarget
  rw [GQ2.ContCoh.sqInitialAlphabetEquiv_handleU]
  rfl

@[simp] theorem frattiniFrameTarget_handleV {h : ℕ} (j : Fin h) :
    frattiniFrameTarget h (SqCore.sqHandleIdxV j) = 1 := by
  unfold frattiniFrameTarget
  rw [GQ2.ContCoh.sqInitialAlphabetEquiv_handleV]
  rfl

/-- At every core/handle position, the coordinate of `(1, 0)` (the adapted image of the
mod-four class `κ`) equals the mod-four parity of the target value. -/
theorem frattiniFrame_match_parity (h : ℕ) (s : Fin 3 ⊕ (Fin h × Fin 2)) :
    modelCoordAt h s ((1 : ZMod 2), 0) =
      Multiplicative.toAdd (unitsModFourParity
        (Units.map (PadicInt.toZModPow 2).toMonoidHom
          (Sum.elim (fun a : Fin 3 =>
              if a = 0 then GQ2.Roe.SvalUnit else if a = 1 then GQ2.Roe.rootXUnit
              else GQ2.Roe.YvalUnit)
            (fun _ => 1) s))) := by
  rcases s with a | p
  · rw [Sum.elim_inl]
    by_cases ha0 : a = 0
    · subst ha0
      rw [if_pos rfl, frattiniFrame_parity_of_val_one frattiniFrame_Sval_modFour]
      simp
    · by_cases ha1 : a = 1
      · subst ha1
        rw [if_neg ha0, if_pos rfl, frattiniFrame_parity_of_val_one frattiniFrame_rootX_modFour]
        simp
      · have ha2 : a = 2 := (by decide : ∀ b : Fin 3, ¬b = 0 → ¬b = 1 → b = 2) a ha0 ha1
        subst ha2
        rw [if_neg ha0, if_neg ha1,
          frattiniFrame_parity_of_val_three frattiniFrame_Yval_modFour]
        simp
  · rw [Sum.elim_inr, map_one, map_one, toAdd_one]
    simp only [modelCoordAt, Sum.elim_inr]
    split_ifs <;> rfl

/-- At every core/handle position, the coordinate of `(0, ((1,1), 0))` (the adapted image of
the mod-eight `ω` class `τ`) equals `ω` of the target value. -/
theorem frattiniFrame_match_omega (h : ℕ) (s : Fin 3 ⊕ (Fin h × Fin 2)) :
    modelCoordAt h s ((0 : ZMod 2), ((1, 1), 0)) =
      Multiplicative.toAdd (unitsModEightOmega
        (Units.map (PadicInt.toZModPow 3).toMonoidHom
          (Sum.elim (fun a : Fin 3 =>
              if a = 0 then GQ2.Roe.SvalUnit else if a = 1 then GQ2.Roe.rootXUnit
              else GQ2.Roe.YvalUnit)
            (fun _ => 1) s))) := by
  rcases s with a | p
  · rw [Sum.elim_inl]
    by_cases ha0 : a = 0
    · subst ha0
      rw [if_pos rfl, frattiniFrame_omega_of_val frattiniFrame_Sval_modEight,
        omegaResidue_table.2.2.1]
      simp
    · by_cases ha1 : a = 1
      · subst ha1
        rw [if_neg ha0, if_pos rfl, frattiniFrame_omega_of_val frattiniFrame_rootX_modEight,
          omegaResidue_table.2.2.1]
        simp
      · have ha2 : a = 2 := (by decide : ∀ b : Fin 3, ¬b = 0 → ¬b = 1 → b = 2) a ha0 ha1
        subst ha2
        rw [if_neg ha0, if_neg ha1, frattiniFrame_omega_of_val frattiniFrame_Yval_modEight,
          omegaResidue_table.2.2.2]
        simp
  · rw [Sum.elim_inr, map_one, map_one, toAdd_one]
    simp only [modelCoordAt, Sum.elim_inr]
    split_ifs <;> rfl

end UnitData

/-! ## §6 Arithmetic classes, the transported cup form, and exact lifting -/

section Arithmetic

open GQ2.HilbertSymbol

variable {K : IntermediateField ℚ_[2] ℚ̄₂} [FiniteDimensional ℚ_[2] K]
  [CompactSpace (GalK K)] [TotallyDisconnectedSpace (GalK K)]

local instance : DistribMulAction (maxProPQuotient 2 (GalK K)) (ZMod 2) :=
  scalarActionZmodTwo _

local instance : ContinuousSMul (maxProPQuotient 2 (GalK K)) (ZMod 2) :=
  scalarActionZmodTwo_continuousSMul _

omit [FiniteDimensional ℚ_[2] K] in
/-- Evaluating the mod-four cyclotomic class is reducing the cyclotomic value mod four. -/
theorem frattiniFrameEval_modFour (g : maxProPQuotient 2 (GalK K)) :
    frattiniFrameEval (cyclotomicModFourClassKTwo (K := K)) g =
      Multiplicative.toAdd (unitsModFourParity
        (Units.map (PadicInt.toZModPow 2).toMonoidHom (chiCycKTwo (K := K) g))) := rfl

omit [FiniteDimensional ℚ_[2] K] in
/-- Evaluating the mod-eight `ω` class is `ω` of the cyclotomic value. -/
theorem frattiniFrameEval_modEight (g : maxProPQuotient 2 (GalK K)) :
    frattiniFrameEval (cyclotomicModEightOmegaClassKTwo (K := K)) g =
      Multiplicative.toAdd (unitsModEightOmega
        (Units.map (PadicInt.toZModPow 3).toMonoidHom (chiCycKTwo (K := K) g))) := rfl

/-- The field cup form, transported to `H¹(G_K(2), 𝔽₂)` through degree-one inflation.
This is by definition the pairing appearing in `IsCupAdapted`. -/
def frattiniFrameCup (x y : H1 (maxProPQuotient 2 (GalK K)) (ZMod 2)) : ZMod 2 :=
  FieldData.cupFormK K (h1MaxProTwoEquivGalK (K := K) x) (h1MaxProTwoEquivGalK (K := K) y)

theorem isCupFormFp2_frattiniFrameCup : IsCupFormFp2 (frattiniFrameCup (K := K)) where
  symm x y := (FieldData.isCupFormFp2_cupFormK K).symm _ _
  add_left x y z := by
    unfold frattiniFrameCup
    rw [map_add]
    exact (FieldData.isCupFormFp2_cupFormK K).add_left _ _ _

theorem nondegFp2_frattiniFrameCup : NondegFp2 (frattiniFrameCup (K := K)) := by
  intro x hx
  have h0 : h1MaxProTwoEquivGalK (K := K) x = 0 := by
    apply FieldData.nondegFp2_cupFormK K
    intro z
    have hz := hx ((h1MaxProTwoEquivGalK (K := K)).symm z)
    rwa [frattiniFrameCup, AddEquiv.apply_symm_apply] at hz
  have := congrArg (h1MaxProTwoEquivGalK (K := K)).symm h0
  rwa [AddEquiv.symm_apply_apply, map_zero] at this

/-- The mod-four class is the Bockstein/Labute vector of the transported cup form. -/
theorem frattiniFrameCup_kappa (x : H1 (maxProPQuotient 2 (GalK K)) (ZMod 2)) :
    frattiniFrameCup (cyclotomicModFourClassKTwo (K := K)) x = frattiniFrameCup x x := by
  unfold frattiniFrameCup
  rw [h1MaxProTwoEquivGalK_cyclotomicModFourClassKTwo, cyclotomicModFourClassK_eq_kappaK]
  exact FieldData.cupFormK_kappa K _

/-- In odd degree, the Labute vector is anisotropic. -/
theorem frattiniFrameCup_kappa_self (hodd : Odd (Module.finrank ℚ_[2] K)) :
    frattiniFrameCup (cyclotomicModFourClassKTwo (K := K))
      (cyclotomicModFourClassKTwo (K := K)) = 1 := by
  unfold frattiniFrameCup
  rw [h1MaxProTwoEquivGalK_cyclotomicModFourClassKTwo, cyclotomicModFourClassK_eq_kappaK]
  exact FieldData.cupFormK_kappa_self K hodd

/-- The `ω` row is orthogonal to the mod-four row (`(2, -1)_K = 1`). -/
theorem frattiniFrameCup_omega_modFour :
    frattiniFrameCup (cyclotomicModEightOmegaClassKTwo (K := K))
      (cyclotomicModFourClassKTwo (K := K)) = 0 := by
  unfold frattiniFrameCup
  rw [h1MaxProTwoEquivGalK_cyclotomicModEightOmegaClassKTwo,
    h1MaxProTwoEquivGalK_cyclotomicModFourClassKTwo]
  exact cupFormK_cyclotomicModEightOmega_modFour (K := K)

/-- The `ω` row is nonzero in odd degree: odd-degree cyclotomic surjectivity realizes the
value `X ≡ 5 (mod 8)`, on which `ω` reads `1`. -/
theorem cyclotomicModEightOmegaClassKTwo_ne_zero
    {R : LocalReciprocity} (B : Dyadic.MarkedRecip R K)
    (hodd : Odd (Module.finrank ℚ_[2] K)) :
    cyclotomicModEightOmegaClassKTwo (K := K) ≠ 0 := by
  intro h0
  obtain ⟨g, hg⟩ := chiCycKTwo_surjective_of_odd_finrank K B hodd GQ2.Roe.rootXUnit
  have h1 : frattiniFrameEval (cyclotomicModEightOmegaClassKTwo (K := K)) g = 0 := by
    rw [h0]
    exact frattiniFrameEval_zero g
  rw [frattiniFrameEval_modEight, hg] at h1
  have hval : ((Units.map (PadicInt.toZModPow 3).toMonoidHom GQ2.Roe.rootXUnit :
      (ZMod 8)ˣ) : ZMod 8) = 5 := frattiniFrame_rootX_modEight
  rw [frattiniFrame_omega_of_val hval, omegaResidue_table.2.2.1] at h1
  exact one_ne_zero h1

omit [FiniteDimensional ℚ_[2] K] in
/-- The sharp mod-eight cyclotomic shadow of a Frattini coset carries exactly the values of
the two arithmetic classes on any representative. -/
theorem frattiniFrame_sharpShadow_data (g : maxProPQuotient 2 (GalK K)) :
    unitsModEightData (SqCyclotomicStageTuple.sharpChiLevel (chiCycKTwo (K := K)) 2 (le_refl 2)
        (levelMk (maxProPQuotient 2 (GalK K)) 2 g)) =
      (frattiniFrameEval (cyclotomicModFourClassKTwo (K := K)) g,
        frattiniFrameEval (cyclotomicModEightOmegaClassKTwo (K := K)) g) := by
  rw [SqCyclotomicStageTuple.sharpChiLevel_levelMk]
  unfold unitsModEightData
  rw [frattiniFrame_unitsMap_cast, frattiniFrameEval_modFour, frattiniFrameEval_modEight]

omit [FiniteDimensional ℚ_[2] K] in
/-- **Exact cyclotomic-value lifting within a Frattini coset.**  If the mod-four and `ω`
classes evaluate on `g'` to the corresponding data of the target unit `u`, sharp exact fibre
lifting replaces `g'` by an element with cyclotomic value exactly `u` in the same coset. -/
theorem frattiniFrameExactLift
    (supply : SqCyclotomicStageTuple.SharpExactLevelFibreLiftSupply (maxProPQuotient 2 (GalK K))
      (chiCycKTwo (K := K)))
    (g' : maxProPQuotient 2 (GalK K)) (u : ℤ_[2]ˣ)
    (h4 : frattiniFrameEval (cyclotomicModFourClassKTwo (K := K)) g' =
      Multiplicative.toAdd (unitsModFourParity
        (Units.map (PadicInt.toZModPow 2).toMonoidHom u)))
    (h8 : frattiniFrameEval (cyclotomicModEightOmegaClassKTwo (K := K)) g' =
      Multiplicative.toAdd (unitsModEightOmega
        (Units.map (PadicInt.toZModPow 3).toMonoidHom u))) :
    ∃ x : maxProPQuotient 2 (GalK K),
      chiCycKTwo (K := K) x = u ∧
        levelMk (maxProPQuotient 2 (GalK K)) 2 x =
          levelMk (maxProPQuotient 2 (GalK K)) 2 g' := by
  have hshadow : SqCyclotomicStageTuple.sharpChiLevel (chiCycKTwo (K := K)) 2 (le_refl 2)
      (levelMk (maxProPQuotient 2 (GalK K)) 2 g') =
        Units.map (PadicInt.toZModPow 3).toMonoidHom u := by
    apply unitsModEightData_injective
    rw [frattiniFrame_sharpShadow_data, h4, h8]
    unfold unitsModEightData
    rw [frattiniFrame_unitsMap_cast]
  obtain ⟨x, hx1, hx2⟩ := supply.lift 2 (le_refl 2) u
    (levelMk (maxProPQuotient 2 (GalK K)) 2 g') hshadow
  exact ⟨x, hx1, hx2.symm⟩

end Arithmetic

end FrattiniFrameSupply

/-! ## §7 The supply theorem -/

open FrattiniFrameSupply in
/-- **The odd-degree cup-adapted Frattini-frame supply.**  For every finite `K/ℚ₂` of odd
degree there is a `SqCyclotomicFrattiniFrame` on `(deg - 1)/2` handles whose dual Frattini
family carries the field cup form to the improved relator's constructor table.

The generators are the exact-cyclotomic-value representatives of the dual family of the
`κ`/`τ`-adapted Witt coordinates of `H¹(G_K(2), 𝔽₂)`. -/
theorem oddDegreeSqCyclotomicFrattiniFrameSupply_holds :
    OddDegreeSqCyclotomicFrattiniFrameSupply := by
  intro K _ _ _ _ hodd
  classical
  letI : DistribMulAction (maxProPQuotient 2 (GalK K)) (ZMod 2) := scalarActionZmodTwo _
  letI : ContinuousSMul (maxProPQuotient 2 (GalK K)) (ZMod 2) :=
    scalarActionZmodTwo_continuousSMul _
  obtain ⟨k, hk⟩ := id hodd
  rw [show (Module.finrank ℚ_[2] K - 1) / 2 = k from by omega]
  -- finiteness and cardinality of `H¹(G_K(2), 𝔽₂)`
  have hfin : Finite (H1 (maxProPQuotient 2 (GalK K)) (ZMod 2)) := by
    apply Nat.finite_of_card_ne_zero
    rw [card_H1_zmodTwo_maxProTwoGalK (K := K)]
    positivity
  haveI := hfin
  have hcard : Nat.card (H1 (maxProPQuotient 2 (GalK K)) (ZMod 2)) = 2 ^ (2 * k + 3) := by
    rw [card_H1_zmodTwo_maxProTwoGalK (K := K),
      show Module.finrank ℚ_[2] K + 2 = 2 * k + 3 from by omega]
  -- the adapted Witt coordinates
  obtain ⟨Φ, hGram, hΦκ, hΦτ⟩ :=
    frattiniFrameAdaptedModelEquiv (isCupFormFp2_frattiniFrameCup (K := K))
      (nondegFp2_frattiniFrameCup (K := K)) (frattiniFrameCup_kappa (K := K))
      (frattiniFrameCup_kappa_self (K := K) hodd) (frattiniFrameCup_omega_modFour (K := K))
      (cyclotomicModEightOmegaClassKTwo_ne_zero (markedRecipAt K) hodd) hcard
  -- realize the adapted coordinate functionals by group elements
  choose gens' hgens' using fun i : Fin (SqCore.sqRank k) =>
    frattiniFrameEval_realizable (K := K) hfin
      ((modelCoordL k (GQ2.ContCoh.sqInitialAlphabetEquiv k i)).comp Φ.toLinearMap)
  have hD : ∀ (i : Fin (SqCore.sqRank k)) (x : H1 (maxProPQuotient 2 (GalK K)) (ZMod 2)),
      frattiniFrameEval x (gens' i) =
        modelCoordAt k (GQ2.ContCoh.sqInitialAlphabetEquiv k i) (Φ x) := fun i x =>
    hgens' i x
  -- exact cyclotomic values in each dual Frattini coset
  have hsupply := SqCyclotomicStageTuple.oddDegreeGalKSq_sharpExactLevelFibreLiftSupply
    (markedRecipAt K) hodd
  have hmatch4 : ∀ i : Fin (SqCore.sqRank k),
      frattiniFrameEval (cyclotomicModFourClassKTwo (K := K)) (gens' i) =
        Multiplicative.toAdd (unitsModFourParity
          (Units.map (PadicInt.toZModPow 2).toMonoidHom (frattiniFrameTarget k i))) := by
    intro i
    rw [hD i, hΦκ]
    exact frattiniFrame_match_parity k (GQ2.ContCoh.sqInitialAlphabetEquiv k i)
  have hmatch8 : ∀ i : Fin (SqCore.sqRank k),
      frattiniFrameEval (cyclotomicModEightOmegaClassKTwo (K := K)) (gens' i) =
        Multiplicative.toAdd (unitsModEightOmega
          (Units.map (PadicInt.toZModPow 3).toMonoidHom (frattiniFrameTarget k i))) := by
    intro i
    rw [hD i, hΦτ]
    exact frattiniFrame_match_omega k (GQ2.ContCoh.sqInitialAlphabetEquiv k i)
  choose gens hχ hlevel using fun i : Fin (SqCore.sqRank k) =>
    frattiniFrameExactLift (K := K) hsupply (gens' i) (frattiniFrameTarget k i)
      (hmatch4 i) (hmatch8 i)
  have hD2 : ∀ (i : Fin (SqCore.sqRank k)) (x : H1 (maxProPQuotient 2 (GalK K)) (ZMod 2)),
      frattiniFrameEval x (gens i) =
        modelCoordAt k (GQ2.ContCoh.sqInitialAlphabetEquiv k i) (Φ x) := fun i x =>
    (frattiniFrameEval_eq_of_levelMk_eq x (hlevel i)).trans (hD i x)
  refine ⟨⟨gens, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · rw [hχ 0, frattiniFrameTarget_zero]
  · rw [hχ 1, frattiniFrameTarget_one]
  · rw [hχ 2, frattiniFrameTarget_two]
  · intro j
    rw [MonoidHom.mem_ker]
    show chiCycKTwo (K := K) (gens (SqCore.sqHandleIdxU j)) = 1
    rw [hχ (SqCore.sqHandleIdxU j), frattiniFrameTarget_handleU]
  · intro j
    rw [MonoidHom.mem_ker]
    show chiCycKTwo (K := K) (gens (SqCore.sqHandleIdxV j)) = 1
    rw [hχ (SqCore.sqHandleIdxV j), frattiniFrameTarget_handleV]
  · -- Frattini generation, by duality
    by_contra hne
    haveI hFfin : Finite (levelQuot (maxProPQuotient 2 (GalK K)) 2) :=
      finite_levelQuot _ (maxProTwoGalK_isTopologicallyFinGen K) isProP_maxProPQuotient 2
    haveI hFdisc : DiscreteTopology (levelQuot (maxProPQuotient 2 (GalK K)) 2) :=
      discreteTopology_levelQuot _ (maxProTwoGalK_isTopologicallyFinGen K)
        isProP_maxProPQuotient 2
    obtain ⟨c, hcH, hcne⟩ := frattiniFrame_exists_modTwo_character
      (frattiniFrame_levelTwo_mul_comm (maxProPQuotient 2 (GalK K)))
      (frattiniFrame_levelTwo_sq (maxProPQuotient 2 (GalK K))) hne
    set cQ : ContinuousMonoidHom (maxProPQuotient 2 (GalK K)) (Multiplicative (ZMod 2)) :=
      ⟨c.comp (levelMk (maxProPQuotient 2 (GalK K)) 2), by
        have h1 : Continuous c := continuous_of_discreteTopology
        exact h1.comp (continuous_levelMk (maxProPQuotient 2 (GalK K)) 2)⟩ with hcQ
    have hvanish : ∀ i, frattiniFrameEval
        (SqCyclotomicFrattiniFrame.characterClass (K := K) cQ) (gens i) = 0 := by
      intro i
      rw [frattiniFrameEval_characterClass]
      show Multiplicative.toAdd (c (levelMk (maxProPQuotient 2 (GalK K)) 2 (gens i))) = 0
      rw [hcH _ (Subgroup.subset_closure ⟨i, rfl⟩)]
      rfl
    have hΦ0 : Φ (SqCyclotomicFrattiniFrame.characterClass (K := K) cQ) = 0 := by
      apply modelCoordAt_eq_zero
      intro s
      have hs := hvanish ((GQ2.ContCoh.sqInitialAlphabetEquiv k).symm s)
      rw [hD2] at hs
      rwa [Equiv.apply_symm_apply] at hs
    have hcc0 : SqCyclotomicFrattiniFrame.characterClass (K := K) cQ = 0 := by
      have hs := congrArg Φ.symm hΦ0
      rwa [LinearEquiv.symm_apply_apply, map_zero] at hs
    apply hcne
    apply MonoidHom.ext
    intro f
    obtain ⟨g, rfl⟩ := levelMk_surjective (maxProPQuotient 2 (GalK K)) 2 f
    have hg : frattiniFrameEval
        (SqCyclotomicFrattiniFrame.characterClass (K := K) cQ) g =
          Multiplicative.toAdd (cQ g) := frattiniFrameEval_characterClass cQ g
    rw [hcc0, frattiniFrameEval_zero] at hg
    show c (levelMk (maxProPQuotient 2 (GalK K)) 2 g) = 1
    have hone : cQ g = 1 := by
      apply Multiplicative.toAdd.injective
      rw [← hg]
      rfl
    exact hone
  · -- cup adaptation
    show ∀ c d : ContinuousMonoidHom (maxProPQuotient 2 (GalK K)) (Multiplicative (ZMod 2)),
      FieldData.cupFormK K
          (h1MaxProTwoEquivGalK (K := K)
            (SqCyclotomicFrattiniFrame.characterClass (K := K) c))
          (h1MaxProTwoEquivGalK (K := K)
            (SqCyclotomicFrattiniFrame.characterClass (K := K) d)) =
        GQ2.ContCoh.sqRelatorQuadraticInitialGram k
          (fun i j => Multiplicative.toAdd (c (gens i)) * Multiplicative.toAdd (d (gens j)))
    intro c d
    have h1 := hGram (SqCyclotomicFrattiniFrame.characterClass (K := K) c)
      (SqCyclotomicFrattiniFrame.characterClass (K := K) d)
    refine h1.trans ?_
    rw [← sqRelatorQuadraticInitialGram_modelCoord]
    congr 1
    funext i j
    rw [← hD2 i (SqCyclotomicFrattiniFrame.characterClass (K := K) c),
      ← hD2 j (SqCyclotomicFrattiniFrame.characterClass (K := K) d),
      frattiniFrameEval_characterClass, frattiniFrameEval_characterClass]

/-- Sanity gate at the base field: the supply specializes to `K = ⊥` and handle count `0`,
consistently with `sqCyclotomicStageTuple_bot_three_nonempty`'s rank-one stage (stated under
the same ambient profinite binders as the rank-one file). -/
example [CompactSpace AbsGalQ2] [T2Space AbsGalQ2] [TotallyDisconnectedSpace AbsGalQ2] :
    ∃ F : SqCyclotomicFrattiniFrame (⊥ : IntermediateField ℚ_[2] ℚ̄₂) 0,
    F.IsCupAdapted := by
  have h := oddDegreeSqCyclotomicFrattiniFrameSupply_holds
    (⊥ : IntermediateField ℚ_[2] ℚ̄₂)
    (by rw [IntermediateField.finrank_bot]; exact odd_one)
  rwa [show (Module.finrank ℚ_[2] (⊥ : IntermediateField ℚ_[2] ℚ̄₂) - 1) / 2 = 0 from by
    rw [IntermediateField.finrank_bot]] at h

#print axioms oddDegreeSqCyclotomicFrattiniFrameSupply_holds

end

end GQ2.Dyadic.LSquare
