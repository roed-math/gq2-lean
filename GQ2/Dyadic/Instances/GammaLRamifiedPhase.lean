/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Codex
-/
import GQ2.Dyadic.Instances.GammaLUnramifiedPhase
import GQ2.Dyadic.Instances.LRamifiedStokes
import GQ2.Dyadic.Instances.LHeisenbergResolver
import GQ2.GaussZ.FinalGammaA.Action

/-!
# The ramified word phase for the improved L presentation

The diagonal of the improved `L_sq` word phase is the Wall double

`qDouble q U x = q x + polar q x (U x)`,

not merely a quadratic refinement inferred from the ramified Hessian.  The word calculation in
`Certificates.L` proves this formula on the head, and the handle tail is a sum of hyperbolic
planes.  This file closes the ensuing finite quadratic-form calculation: an Arf-zero Wall head
has the positive ramified Gauss value, and the action-level ramified theorem proves that its Arf
invariant is zero in the simple `q = 2` tame case.

The final sections expose normal coordinates on ramified word `H¹` and isolate the only remaining
source seam as one pointwise identity between `QZeroBar` and this explicit word phase.  Thus no
quotient-surjectivity, normal-form, reindexing, Arf, or downstream Gauss algebra is hidden in the
remaining determinant-phase obligation.

All headline declarations in this file were audited with `#print axioms`; each depends on exactly
the standard three axioms `[propext, Classical.choice, Quot.sound]`.
-/

namespace GQ2.Dyadic.LSquare

noncomputable section

open GQ2 GQ2.SectionEight
open SectionSeven AffineTLift CentralObstruction ContCoh FoxH
open GQ2.Dyadic GQ2.Dyadic.Words GQ2.Dyadic.Words.LSq
open GQ2.Dyadic.Certificates GQ2.Dyadic.Certificates.LSqStokes
open GQ2.Dyadic.Count
open GQ2.QuadraticFp2

/-! ## The evaluated quadratic diagonal -/

/-- The complete evaluated `L_sq` word is the Wall quadratic diagonal together with the ordered
handle planes.  Unlike `LRamifiedHessian`, this is an identity of quadratic values, not merely
an identity of their polar pairings. -/
theorem hessRelZ_lSq_eq_wallHandlePhase
    {C V : Type} [Group C] [AddCommGroup V] [DistribMulAction C V]
    {q : V → ZMod 2} (dat : FactorSet C V) (hdat : IsEquivariantFactorSet q dat)
    {h : ℕ} (hV2 : ∀ v : V, v + v = 0) (s u : C)
    (v : Fin (2 * h + 1 + 1) → V) (hv0 : v (lSqIdx0 h) = 0)
    (E : Zhat → ℤ) (E₂ : ℤ_[2] → ℤ) :
    hessRelZ (lSqHessMark s u v) (kappa0Cocycle dat hdat) E E₂ (lSqW h) =
      lSqWallHandlePhase q (smulAddEquiv ((s ^ E omega2)⁻¹)) h
        (v (lSqIdx1 h), fun j => (v (lSqIdxU j), v (lSqIdxV j))) := by
  rw [hessRelZ_lSq dat hdat hV2 s u v hv0 E E₂]
  rfl

/-! ## The positive Arf/Gauss branch -/

/-- A nonsingular quadratic form of Arf invariant zero has the positive Gauss sign. -/
theorem gaussSum_eq_pos_pow_of_arf_zero
    {V : Type} [AddCommGroup V] [Fintype V]
    (q : V → ZMod 2) (hq : IsQuadraticFp2 q) (hns : Nonsingular q)
    {m : ℕ} (hcard : Fintype.card V = 2 ^ (2 * m)) (harf : arf q = 0) :
    QuadraticFp2.gaussSum q = (2 ^ m : ℤ) := by
  rcases gaussSum_eq_pow q hq hns hcard with hpos | hneg
  · exact hpos
  · have hpos' := (arf_eq_zero_iff_gaussSum_pos q).mp harf
    rw [hneg] at hpos'
    have hp : 0 < (2 ^ m : ℤ) := by positivity
    omega

/-- The positive candidate zero count forces Arf invariant zero. -/
theorem arf_eq_zero_of_zeroCount_add
    {V : Type} [AddCommGroup V] [Fintype V]
    (q : V → ZMod 2) {m : ℕ} (hm : 1 ≤ m)
    (hcard : Fintype.card V = 2 ^ (2 * m))
    (hzero : zeroCount q = 2 ^ (2 * m - 1) + 2 ^ (m - 1)) : arf q = 0 := by
  rw [arf, hzero, Nat.card_eq_fintype_card, hcard]
  rw [if_pos]
  have hpow : 0 < 2 ^ (m - 1) := pow_pos (by omega) _
  have htwod : 2 * 2 ^ (2 * m - 1) = 2 ^ (2 * m) := by
    rw [← pow_succ']
    congr 1
    omega
  rw [Nat.mul_add, htwod]
  omega

/-- An Arf-zero Wall head, followed by `h` hyperbolic handle planes, has the complete positive
ramified Gauss value.  This is the full finite quadratic-form endpoint, not just its polar
Hessian. -/
theorem lSqWallHandlePhase_gaussSum_of_arf_zero
    {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Fintype V]
    {q : V → ZMod 2}
    (hq : IsQuadraticFp2 q) (hns : Nonsingular q)
    (h2 : ∀ v : V, v + v = 0) {m : ℕ}
    (hcard : Fintype.card V = 2 ^ (2 * m))
    (U : V ≃+ V) (hUq : ∀ v, q (U v) = q v)
    (hU2 : ∃ n, (⇑U)^[2 ^ n] = id)
    (harf : arf (qDouble q U) = 0) (h : ℕ) :
    QuadraticFp2.gaussSum (lSqWallHandlePhase q U h) =
      (2 ^ (m * (2 * h + 1)) : ℤ) := by
  change QuadraticFp2.gaussSum (fun p : V × (Fin h → V × V) =>
    qDouble q U p.1 + ∑ j, polar q (p.2 j).1 (p.2 j).2) =
      (2 ^ (m * (2 * h + 1)) : ℤ)
  rw [lSq_handle_form_gaussSum hq hns hcard (qDouble q U) h,
    gaussSum_eq_pos_pow_of_arf_zero (qDouble q U)
      (isQuadraticFp2_qDouble q U hq h2 hUq)
      (qDouble_nonsingular q U hq h2 hns hUq hU2) hcard harf]
  have hexp : m * (2 * h + 1) = m + 2 * m * h := by ring
  rw [hexp, pow_add]

/-- The positive endpoint value in the `SourceNumerics` spelling consumed by the determinant
certificate. -/
theorem lSqWallHandlePhase_gaussSum_standardRam
    {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Fintype V]
    {q : V → ZMod 2}
    (hq : IsQuadraticFp2 q) (hns : Nonsingular q)
    (h2 : ∀ v : V, v + v = 0) {m : ℕ}
    (hcard : Fintype.card V = 2 ^ (2 * m))
    (U : V ≃+ V) (hUq : ∀ v, q (U v) = q v)
    (hU2 : ∃ n, (⇑U)^[2 ^ n] = id)
    (harf : arf (qDouble q U) = 0) (h : ℕ) :
    QuadraticFp2.gaussSum (lSqWallHandlePhase q U h) =
      (standardNumerics (2 * h + 1)).gaussRam m := by
  rw [lSqWallHandlePhase_gaussSum_of_arf_zero hq hns h2 hcard U hUq hU2 harf h]
  change (2 : ℤ) ^ (m * (2 * h + 1)) = (2 : ℤ) ^ ((2 * h + 1) * m)
  rw [Nat.mul_comm]

/-! ## Concrete ramified closure from the tame action -/

/-- In the simple ramified `Ttame` action, the *actual quadratic diagonal* of the improved head
has Arf invariant zero, and the full head-plus-handles endpoint has the standard positive
ramified Gauss value.  The first conclusion is obtained from the proved ramified zero count for
the explicit function `qDouble q (powOmega2 (c tameSigma) • ·)`, so it does not infer the Arf
sign from the polar Hessian. -/
theorem lSqWallHandlePhase_ramified_of_action
    {C : Type} [Group C] [TopologicalSpace C] [DiscreteTopology C] [Finite C]
    {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Fintype V]
    [DistribMulAction C V]
    (c : ContinuousMonoidHom Ttame C) (hc : Function.Surjective ⇑c)
    (hsimple : ∀ W : AddSubgroup V,
      (∀ (g : C), ∀ w ∈ W, g • w ∈ W) → W = ⊥ ∨ W = ⊤)
    (hram : ∃ v : V, c tameTau • v ≠ v)
    (q : V → ZMod 2) (hq : IsQuadraticFp2 q) (hns : Nonsingular q)
    (hinv : IsInvariant C q)
    (m : ℕ) (hm : 1 ≤ m) (hcard : Fintype.card V = 2 ^ (2 * m)) (h : ℕ) :
    let U : V ≃+ V := DistribMulAction.toAddEquiv V (powOmega2 (c tameSigma))
    arf (qDouble q U) = 0 ∧
      QuadraticFp2.gaussSum (lSqWallHandlePhase q U h) =
        (standardNumerics (2 * h + 1)).gaussRam m := by
  let U : V ≃+ V := DistribMulAction.toAddEquiv V (powOmega2 (c tameSigma))
  have hcard' : Nat.card V = 2 ^ (2 * m) := by
    simpa only [Nat.card_eq_fintype_card] using hcard
  have hUfun : (⇑U : V → V) = fun x => powOmega2 (c tameSigma) • x := by
    funext x
    rfl
  have hzero := zeroCount_qDouble_ramified_of_action c hc hsimple hram q hq hns hinv
    m hm hcard'
  have harf : arf (qDouble q U) = 0 := by
    apply arf_eq_zero_of_zeroCount_add (qDouble q U) hm hcard
    rw [hUfun]
    exact hzero
  refine ⟨harf, ?_⟩
  change QuadraticFp2.gaussSum (fun p : V × (Fin h → V × V) =>
    qDouble q U p.1 + ∑ j, polar q (p.2 j).1 (p.2 j).2) =
      (standardNumerics (2 * h + 1)).gaussRam m
  rw [lSq_handle_form_gaussSum hq hns hcard (qDouble q U) h]
  have hhead : QuadraticFp2.gaussSum (qDouble q U) = (2 ^ m : ℤ) := by
    rw [QuadraticFp2.gaussSum, ← finsum_eq_sum_of_fintype]
    have hsum :=
      finsum_sign_ramified_of_action c hc hsimple hram q hq hns hinv m hm hcard'
    simp_rw [sectionEight_sign_eq_quadraticSign] at hsum
    rw [hUfun]
    exact hsum
  rw [hhead]
  change (2 : ℤ) ^ m * 2 ^ (2 * m * h) = (2 : ℤ) ^ ((2 * h + 1) * m)
  rw [← pow_add]
  congr 1
  ring

/-! ## Ramified word cohomology in normal coordinates -/

/-- The class of a chosen normal representative in middle Stokes cohomology. -/
def stokesH1NormalClass
    {K₀ K₁ K₂ P : Type*} [AddCommGroup K₀] [AddCommGroup K₁] [AddCommGroup K₂]
    (d₀ : K₀ →+ K₁) (d₁ : K₁ →+ K₂) (normal : P → K₁)
    (hmem : ∀ p, d₁ (normal p) = 0) (p : P) : StokesH1 d₀ d₁ :=
  stokesH1Mk d₀ d₁ ⟨normal p, AddMonoidHom.mem_ker.mpr (hmem p)⟩

/-- A unique family of normal representatives gives an actual coordinate equivalence on `H¹`,
strengthening the cardinality-only normal-form theorem. -/
theorem stokesH1NormalClass_bijective
    {K₀ K₁ K₂ P : Type*} [AddCommGroup K₀] [AddCommGroup K₁] [AddCommGroup K₂]
    (d₀ : K₀ →+ K₁) (d₁ : K₁ →+ K₂) (normal : P → K₁)
    (hmem : ∀ p, d₁ (normal p) = 0)
    (hnf : ∀ x, d₁ x = 0 → ∃! p, x - normal p ∈ Set.range d₀) :
    Function.Bijective (stokesH1NormalClass d₀ d₁ normal hmem) := by
  have key : ∀ (a b : ↥d₁.ker),
      stokesH1Mk d₀ d₁ a = stokesH1Mk d₀ d₁ b ↔
        b.val - a.val ∈ Set.range d₀ := by
    intro a b
    show QuotientAddGroup.mk a = QuotientAddGroup.mk b ↔ _
    rw [QuotientAddGroup.eq, AddSubgroup.mem_addSubgroupOf]
    show -a.val + b.val ∈ d₀.range ↔ b.val - a.val ∈ Set.range d₀
    rw [show -a.val + b.val = b.val - a.val from by abel]
    exact AddMonoidHom.mem_range
  constructor
  · intro p p' hpp
    change stokesH1Mk d₀ d₁ ⟨normal p, AddMonoidHom.mem_ker.mpr (hmem p)⟩ =
      stokesH1Mk d₀ d₁ ⟨normal p', AddMonoidHom.mem_ker.mpr (hmem p')⟩ at hpp
    rw [key] at hpp
    obtain ⟨p₀, -, huniq⟩ := hnf (normal p) (hmem p)
    have hp : p = p₀ := huniq p (show normal p - normal p ∈ Set.range d₀ from
      ⟨0, by simp⟩)
    have hp' : p' = p₀ := huniq p' (by
      obtain ⟨v, hv⟩ := hpp
      refine ⟨-v, ?_⟩
      rw [map_neg, hv]
      abel)
    exact hp.trans hp'.symm
  · intro H
    obtain ⟨x, rfl⟩ := stokesH1Mk_surjective d₀ d₁ H
    obtain ⟨p, hp, -⟩ := hnf x.val (AddMonoidHom.mem_ker.mp x.2)
    refine ⟨p, ?_⟩
    change stokesH1Mk d₀ d₁ ⟨normal p, AddMonoidHom.mem_ker.mpr (hmem p)⟩ =
      stokesH1Mk d₀ d₁ x
    exact (key ⟨normal p, AddMonoidHom.mem_ker.mpr (hmem p)⟩ x).mpr hp

/-- The coordinate equivalence induced by unique normal representatives. -/
noncomputable def stokesH1NormalEquiv
    {K₀ K₁ K₂ P : Type*} [AddCommGroup K₀] [AddCommGroup K₁] [AddCommGroup K₂]
    (d₀ : K₀ →+ K₁) (d₁ : K₁ →+ K₂) (normal : P → K₁)
    (hmem : ∀ p, d₁ (normal p) = 0)
    (hnf : ∀ x, d₁ x = 0 → ∃! p, x - normal p ∈ Set.range d₀) :
    StokesH1 d₀ d₁ ≃ P :=
  (Equiv.ofBijective (stokesH1NormalClass d₀ d₁ normal hmem)
    (stokesH1NormalClass_bijective d₀ d₁ normal hmem hnf)).symm

@[simp] theorem stokesH1NormalEquiv_normalClass
    {K₀ K₁ K₂ P : Type*} [AddCommGroup K₀] [AddCommGroup K₁] [AddCommGroup K₂]
    (d₀ : K₀ →+ K₁) (d₁ : K₁ →+ K₂) (normal : P → K₁)
    (hmem : ∀ p, d₁ (normal p) = 0)
    (hnf : ∀ x, d₁ x = 0 → ∃! p, x - normal p ∈ Set.range d₀) (p : P) :
    stokesH1NormalEquiv d₀ d₁ normal hmem hnf
      (stokesH1NormalClass d₀ d₁ normal hmem p) = p := by
  exact (Equiv.ofBijective (stokesH1NormalClass d₀ d₁ normal hmem)
    (stokesH1NormalClass_bijective d₀ d₁ normal hmem hnf)).symm_apply_apply p

/-- Reindex the two coordinates of every handle as an actual pair. -/
def handlePairsAddEquiv {h : ℕ} {A : Type*} [AddCommGroup A] :
    (Fin h × Fin 2 → A) ≃+ (Fin h → A × A) where
  toFun z := fun j => (z (j, 0), z (j, 1))
  invFun z := fun jk => (finTwoProdAddEquiv.symm (z jk.1)) jk.2
  left_inv z := by
    funext jk
    rcases jk with ⟨j, k⟩
    fin_cases k <;> rfl
  right_inv z := by
    funext j
    rfl
  map_add' z z' := by
    funext j
    rfl

/-- Ramified word `H¹` is exactly one Wall-head coordinate and `h` handle pairs.  This upgrades
`lSqFam_ramified_normalForm` from a cardinality computation to the equivalence required for a
source/word phase comparison. -/
noncomputable def lSqRamifiedWordH1Equiv
    {h q : ℕ} {C A : Type*} [Group C] [Finite C] [AddCommGroup A] [Finite A]
    [DistribMulAction C A]
    (t : Marking (2 * h + 1) C) (hA₂ : ∀ a : A, a + a = 0)
    (ht : t.TameRelAt q)
    (hwild : ∀ (i : Fin (2 * h + 1 + 1)) (a : A), t.x i • a = a)
    (hτfpf : ∀ a : A, t.τ • a = a → a = 0)
    (hTodd : ∀ a : A, powOmega2 t.τ • a = a)
    (hL : PWord.evalZ ⇑t
      (fun _ ↦ (omega2Exp (4 * Monoid.exponent C) : ℤ))
      (fun _ ↦ (omega2Exp (4 * Monoid.exponent C) : ℤ)) (lSqW h) = 1) :
    WordH1 (⇑t)
        (Certificates.LSqStokes.lSqFam h q
          (omega2Exp (4 * Monoid.exponent C))) A ≃
      A × (Fin h → A × A) :=
  (stokesH1NormalEquiv
      (heisD0 (A := A) ⇑t)
      (heisD1 ⇑t (Certificates.LSqStokes.lSqFam h q
        (omega2Exp (4 * Monoid.exponent C))))
      (fun p : A × (Fin h × Fin 2 → A) => lSqRamifiedNormal h p.1 p.2)
      (fun p => heisD1_lSqRamifiedNormal_eq_zero t hA₂ ht hwild hτfpf hTodd p.1 p.2)
      (lSqFam_ramified_normalForm t hA₂ ht hwild hτfpf hTodd hL)).trans
    ((Equiv.refl A).prodCongr handlePairsAddEquiv.toEquiv)

/-- Regression theorem: the ramified `H¹` equivalence sends the class of the displayed normal
cochain to exactly its Wall coordinate and ordered handle pairs. -/
@[simp] theorem lSqRamifiedWordH1Equiv_normalClass
    {h q : ℕ} {C A : Type*} [Group C] [Finite C] [AddCommGroup A] [Finite A]
    [DistribMulAction C A]
    (t : Marking (2 * h + 1) C) (hA₂ : ∀ a : A, a + a = 0)
    (ht : t.TameRelAt q)
    (hwild : ∀ (i : Fin (2 * h + 1 + 1)) (a : A), t.x i • a = a)
    (hτfpf : ∀ a : A, t.τ • a = a → a = 0)
    (hTodd : ∀ a : A, powOmega2 t.τ • a = a)
    (hL : PWord.evalZ ⇑t
      (fun _ ↦ (omega2Exp (4 * Monoid.exponent C) : ℤ))
      (fun _ ↦ (omega2Exp (4 * Monoid.exponent C) : ℤ)) (lSqW h) = 1)
    (d : A) (z : Fin h × Fin 2 → A) :
    lSqRamifiedWordH1Equiv t hA₂ ht hwild hτfpf hTodd hL
      (stokesH1Mk
        (heisD0 (A := A) ⇑t)
        (heisD1 ⇑t (Certificates.LSqStokes.lSqFam h q
          (omega2Exp (4 * Monoid.exponent C))))
        ⟨lSqRamifiedNormal h d z,
          AddMonoidHom.mem_ker.mpr
            (heisD1_lSqRamifiedNormal_eq_zero t hA₂ ht hwild hτfpf hTodd d z)⟩) =
      (d, fun j => (z (j, 0), z (j, 1))) := by
  unfold lSqRamifiedWordH1Equiv
  rw [Equiv.trans_apply]
  have hnormal := stokesH1NormalEquiv_normalClass
    (heisD0 (A := A) ⇑t)
    (heisD1 ⇑t (Certificates.LSqStokes.lSqFam h q
      (omega2Exp (4 * Monoid.exponent C))))
    (fun p : A × (Fin h × Fin 2 → A) => lSqRamifiedNormal h p.1 p.2)
    (fun p => heisD1_lSqRamifiedNormal_eq_zero t hA₂ ht hwild hτfpf hTodd p.1 p.2)
    (lSqFam_ramified_normalForm t hA₂ ht hwild hτfpf hTodd hL) (d, z)
  simp only [stokesH1NormalClass] at hnormal
  rw [hnormal]
  rfl

/-! ## The one remaining source-to-word identity -/

/-- The marking of a finite target obtained from the canonical generators of `GammaL`. -/
def lTargetMarking
    {h q : ℕ} {C : Type} [Group C] [TopologicalSpace C]
    (rho : ContinuousMonoidHom ((gamma h q : Type)) C) : Marking (2 * h + 1) C :=
  ⟨fun i => rho (gammaGen (2 * h + 1) q (lSqW h) i)⟩

/-- Compose the proved source `H¹` comparison with ramified normal coordinates.  Consequently
the equivalence called `e` in `LRamifiedPointwisePhaseIdentity` is not an additional conjecture:
it is constructed from the existing L presentation and normal-form theorems. -/
noncomputable def lSqRamifiedSourceH1Equiv
    {h q : ℕ} {C A : Type}
    [Group C] [TopologicalSpace C] [DiscreteTopology C] [Finite C]
    [AddCommGroup A] [TopologicalSpace A] [IsTopologicalAddGroup A]
    [DiscreteTopology A] [Finite A]
    [DistribMulAction ((gamma h q : Type)) A]
    [ContinuousSMul ((gamma h q : Type)) A]
    [DistribMulAction C A]
    (rho : ContinuousMonoidHom ((gamma h q : Type)) C)
    (hcompat : ∀ (g : (gamma h q : Type)) (a : A), g • a = rho g • a)
    (hA₂ : ∀ a : A, a + a = 0)
    (hres : ResolvesAt (gammaFam (2 * h + 1) q (lSqW h))
      (Certificates.LSqStokes.lSqFam h q (omega2Exp (4 * Monoid.exponent C)))
      (WordLift A C))
    (ht : (lTargetMarking (h := h) (q := q) rho).TameRelAt q)
    (hwild : ∀ (i : Fin (2 * h + 1 + 1)) (a : A),
      (lTargetMarking (h := h) (q := q) rho).x i • a = a)
    (hτfpf : ∀ a : A, (lTargetMarking (h := h) (q := q) rho).τ • a = a → a = 0)
    (hTodd : ∀ a : A,
      powOmega2 (lTargetMarking (h := h) (q := q) rho).τ • a = a)
    (hL : PWord.evalZ ⇑(lTargetMarking (h := h) (q := q) rho)
      (fun _ ↦ (omega2Exp (4 * Monoid.exponent C) : ℤ))
      (fun _ ↦ (omega2Exp (4 * Monoid.exponent C) : ℤ)) (lSqW h) = 1) :
    H1 (gamma h q : Type) A ≃ A × (Fin h → A × A) :=
  (lSourceH1Equiv rho hcompat hA₂ hres).toEquiv.trans
    (lSqRamifiedWordH1Equiv (lTargetMarking (h := h) (q := q) rho)
      hA₂ ht hwild hτfpf hTodd hL)

/-- The exact remaining ramified phase assertion.  All maps in this formula have already been
constructed: `h1OfVQuot` is the canonical `Z¹/B¹ → H¹` map, `e` is the source-to-normal-word
coordinate equivalence, and `lSqWallHandlePhase` is the evaluated quadratic diagonal proved by
the word Hessian calculation. -/
def LRamifiedPointwisePhaseIdentity
    {Bg : Type} [Group Bg] [Finite Bg] [TopologicalSpace Bg] [DiscreteTopology Bg]
    {D : RadicalCoverData Bg} {DD : DescData D}
    {Gamma : Type} [Group Gamma] [TopologicalSpace Gamma]
    {rho : ContinuousMonoidHom Gamma (Bg ⧸ D.M)}
    [TopologicalSpace DD.Vmod] [DiscreteTopology DD.Vmod]
    [DistribMulAction Gamma DD.Vmod]
    [DistribMulAction Gamma (ZMod 2)]
    (htriv : ∀ (g : Gamma) (a : ZMod 2), g • a = a)
    (hcomp : ∀ (g : Gamma) (v : DD.Vmod), g • v = rho0 DD rho g • v)
    (qWord : DD.Vmod → ZMod 2) (U : DD.Vmod ≃+ DD.Vmod) (h : ℕ)
    (e : H1 Gamma DD.Vmod ≃ DD.Vmod × (Fin h → DD.Vmod × DD.Vmod)) : Prop :=
  ∀ x, QZeroBar DD rho htriv x =
    lSqWallHandlePhase qWord U h (e (h1OfVQuot hcomp x))

/-- Once the displayed pointwise identity is known, the source/word phase comparison is
canonical.  In particular, no further quotient or reindexing argument remains. -/
noncomputable def sourceWordPhaseComparison_of_lRamifiedPointwise
    {Bg : Type} [Group Bg] [Finite Bg] [TopologicalSpace Bg] [DiscreteTopology Bg]
    {D : RadicalCoverData Bg} {DD : DescData D}
    {Gamma : Type} [Group Gamma] [TopologicalSpace Gamma]
    {rho : ContinuousMonoidHom Gamma (Bg ⧸ D.M)}
    [TopologicalSpace DD.Vmod] [DiscreteTopology DD.Vmod]
    [DistribMulAction Gamma DD.Vmod]
    [DistribMulAction Gamma (ZMod 2)]
    (htriv : ∀ (g : Gamma) (a : ZMod 2), g • a = a)
    [Fintype DD.Vmod]
    (hcomp : ∀ (g : Gamma) (v : DD.Vmod), g • v = rho0 DD rho g • v)
    (qWord : DD.Vmod → ZMod 2) (U : DD.Vmod ≃+ DD.Vmod) (h : ℕ)
    (e : H1 Gamma DD.Vmod ≃ DD.Vmod × (Fin h → DD.Vmod × DD.Vmod))
    (hphase : LRamifiedPointwisePhaseIdentity htriv hcomp qWord U h e) :
    SourceWordPhaseComparison DD rho htriv
      (DD.Vmod × (Fin h → DD.Vmod × DD.Vmod))
      (lSqWallHandlePhase qWord U h) :=
  SourceWordPhaseComparison.ofH1Equiv htriv hcomp e hphase

/-- All ramified Gauss algebra downstream of the pointwise identity, in one theorem.  The sole
phase-specific hypothesis is `hphase`; `harf` is the already-isolated arithmetic assertion that
the explicit Wall diagonal has Arf zero. -/
theorem lRamifiedPhasePackage_standardRam_of_pointwise
    {Bg : Type} [Group Bg] [Finite Bg] [TopologicalSpace Bg] [DiscreteTopology Bg]
    {D : RadicalCoverData Bg} {DD : DescData D}
    {Gamma : Type} [Group Gamma] [TopologicalSpace Gamma]
    {rho : ContinuousMonoidHom Gamma (Bg ⧸ D.M)}
    [TopologicalSpace DD.Vmod] [DiscreteTopology DD.Vmod]
    [DistribMulAction Gamma DD.Vmod]
    [DistribMulAction Gamma (ZMod 2)]
    (htriv : ∀ (g : Gamma) (a : ZMod 2), g • a = a)
    [Module (ZMod 2) DD.Vmod] [Fintype DD.Vmod]
    (hcomp : ∀ (g : Gamma) (v : DD.Vmod), g • v = rho0 DD rho g • v)
    (qWord : DD.Vmod → ZMod 2)
    (hq : IsQuadraticFp2 qWord) (hns : Nonsingular qWord)
    (h2 : ∀ v : DD.Vmod, v + v = 0)
    (m : ℕ) (hcard : Fintype.card DD.Vmod = 2 ^ (2 * m))
    (U : DD.Vmod ≃+ DD.Vmod) (hUq : ∀ v, qWord (U v) = qWord v)
    (hU2 : ∃ n, (⇑U)^[2 ^ n] = id)
    (harf : arf (qDouble qWord U) = 0) (h : ℕ)
    (e : H1 Gamma DD.Vmod ≃ DD.Vmod × (Fin h → DD.Vmod × DD.Vmod))
    (hphase : LRamifiedPointwisePhaseIdentity htriv hcomp qWord U h e) :
    Nonempty (SourceWordPhaseComparison DD rho htriv
        (DD.Vmod × (Fin h → DD.Vmod × DD.Vmod))
        (lSqWallHandlePhase qWord U h)) ∧
      QuadraticFp2.gaussSum (lSqWallHandlePhase qWord U h) =
        (standardNumerics (2 * h + 1)).gaussRam m := by
  exact ⟨⟨sourceWordPhaseComparison_of_lRamifiedPointwise
      htriv hcomp qWord U h e hphase⟩,
    lSqWallHandlePhase_gaussSum_standardRam
      hq hns h2 hcard U hUq hU2 harf h⟩

/-- The strongest unconditional `q = 2` ramified package available from the current
formalization.  Simple ramified tame action hypotheses prove the Arf-zero assertion internally;
after that, the only phase comparison hypothesis is the displayed pointwise identity. -/
theorem lRamifiedPhasePackage_of_action_pointwise
    {Bg : Type} [Group Bg] [Finite Bg] [TopologicalSpace Bg] [DiscreteTopology Bg]
    {D : RadicalCoverData Bg} {DD : DescData D}
    {Gamma : Type} [Group Gamma] [TopologicalSpace Gamma]
    {rho : ContinuousMonoidHom Gamma (Bg ⧸ D.M)}
    [TopologicalSpace DD.Vmod] [DiscreteTopology DD.Vmod]
    [DistribMulAction Gamma DD.Vmod]
    [DistribMulAction Gamma (ZMod 2)]
    (htriv : ∀ (g : Gamma) (a : ZMod 2), g • a = a)
    {C : Type} [Group C] [TopologicalSpace C] [DiscreteTopology C] [Finite C]
    [Module (ZMod 2) DD.Vmod] [Fintype DD.Vmod]
    [DistribMulAction C DD.Vmod]
    (hcomp : ∀ (g : Gamma) (v : DD.Vmod), g • v = rho0 DD rho g • v)
    (c : ContinuousMonoidHom Ttame C) (hc : Function.Surjective ⇑c)
    (hsimple : ∀ W : AddSubgroup DD.Vmod,
      (∀ (g : C), ∀ w ∈ W, g • w ∈ W) → W = ⊥ ∨ W = ⊤)
    (hram : ∃ v : DD.Vmod, c tameTau • v ≠ v)
    (qWord : DD.Vmod → ZMod 2)
    (hq : IsQuadraticFp2 qWord) (hns : Nonsingular qWord)
    (hinv : IsInvariant C qWord)
    (m : ℕ) (hm : 1 ≤ m)
    (hcard : Fintype.card DD.Vmod = 2 ^ (2 * m)) (h : ℕ)
    (e : H1 Gamma DD.Vmod ≃ DD.Vmod × (Fin h → DD.Vmod × DD.Vmod))
    (hphase : LRamifiedPointwisePhaseIdentity htriv hcomp qWord
      (DistribMulAction.toAddEquiv DD.Vmod (powOmega2 (c tameSigma))) h e) :
    Nonempty (SourceWordPhaseComparison DD rho htriv
        (DD.Vmod × (Fin h → DD.Vmod × DD.Vmod))
        (lSqWallHandlePhase qWord
          (DistribMulAction.toAddEquiv DD.Vmod (powOmega2 (c tameSigma))) h)) ∧
      arf (qDouble qWord
        (DistribMulAction.toAddEquiv DD.Vmod (powOmega2 (c tameSigma)))) = 0 ∧
      QuadraticFp2.gaussSum (lSqWallHandlePhase qWord
          (DistribMulAction.toAddEquiv DD.Vmod (powOmega2 (c tameSigma))) h) =
        (standardNumerics (2 * h + 1)).gaussRam m := by
  let U : DD.Vmod ≃+ DD.Vmod :=
    DistribMulAction.toAddEquiv DD.Vmod (powOmega2 (c tameSigma))
  have hword := lSqWallHandlePhase_ramified_of_action
    c hc hsimple hram qWord hq hns hinv m hm hcard h
  exact ⟨⟨sourceWordPhaseComparison_of_lRamifiedPointwise
      htriv hcomp qWord U h e hphase⟩, hword⟩

end

end GQ2.Dyadic.LSquare
