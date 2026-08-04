/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, and OpenAI Codex
-/
import GQ2.Dyadic.FiniteTwoLocalReciprocityHigherMuNDual

/-!
# The explicit higher Kummer boundary

This file constructs the connecting class `Kˣ → H¹(G_K, μ_n)` directly from an `n`th root in
`ℚbar2`.  It proves continuity, the cocycle identity, root independence, multiplicativity, and
the exact kernel `(Kˣ)^n` without class field theory or an Artin map.

Surjectivity is separated cleanly: `MuNContinuousHilbert90 K n` asks only for Hilbert 90 on the
finite, discrete-image cocycles `G_K → μ_n` that actually occur in the Kummer argument, and
`higherKummerClassDataOfMuNContinuousHilbert90` turns that theorem into the abstract
`HigherKummerClassData` consumed by the reciprocity layer.  This finite-image restriction is
essential: arbitrary cocycles into the p-adically topologized group `ℚbar2ˣ` need not factor
through a finite quotient.
-/

namespace GQ2.Dyadic

open ContCoh
open scoped Classical

noncomputable section

local notation "ℚbar2" => AlgebraicClosure ℚ_[2]

variable {K : IntermediateField ℚ_[2] ℚbar2} [FiniteDimensional ℚ_[2] K]

def unitInQbar (a : (↥K)ˣ) : ℚbar2ˣ := Units.map K.subtype a

@[simp] theorem unitInQbar_val (a : (↥K)ˣ) : (unitInQbar a : ℚbar2) = (a : ↥K) := rfl

theorem fixing_smul_unitInQbar (g : ↥(K.fixingSubgroup)) (a : (↥K)ˣ) :
    g • unitInQbar a = unitInQbar a := by
  apply Units.ext
  change g.1 (a : ↥K) = (a : ↥K)
  exact g.2 a.1

noncomputable def higherRoot (n : ℕ) [NeZero n] (a : (↥K)ˣ) : ℚbar2 :=
  (IsAlgClosed.exists_pow_nat_eq (unitInQbar a : ℚbar2) (n := n)
    (Nat.pos_of_ne_zero (NeZero.ne n))).choose

theorem higherRoot_pow (n : ℕ) [NeZero n] (a : (↥K)ˣ) :
  higherRoot n a ^ n = unitInQbar a :=
  (IsAlgClosed.exists_pow_nat_eq (unitInQbar a : ℚbar2) (n := n)
    (Nat.pos_of_ne_zero (NeZero.ne n))).choose_spec

theorem higherRoot_ne_zero (n : ℕ) [NeZero n] (a : (↥K)ˣ) :
    higherRoot n a ≠ 0 := by
  intro h
  have := higherRoot_pow n a
  rw [h, zero_pow (NeZero.ne n)] at this
  exact (unitInQbar a).ne_zero (by simpa using this.symm)

noncomputable def higherRootUnit (n : ℕ) [NeZero n] (a : (↥K)ˣ) : ℚbar2ˣ :=
  Units.mk0 (higherRoot n a) (higherRoot_ne_zero n a)

@[simp] theorem higherRootUnit_val (n : ℕ) [NeZero n] (a : (↥K)ˣ) :
    (higherRootUnit n a : ℚbar2) = higherRoot n a := rfl

theorem higherRootUnit_pow (n : ℕ) [NeZero n] (a : (↥K)ˣ) :
    higherRootUnit n a ^ n = unitInQbar a := by
  apply Units.ext
  exact higherRoot_pow n a

def rootRatio (n : ℕ) [NeZero n] (a : (↥K)ˣ) (alpha : ℚbar2ˣ)
    (halpha : alpha ^ n = unitInQbar (K := K) a)
    (g : ↥(K.fixingSubgroup)) : MuN n := by
  let u : ℚbar2ˣ := (g • alpha) * alpha⁻¹
  exact Additive.ofMul ⟨u, by
    rw [mem_rootsOfUnity]
    rw [mul_pow, inv_pow, ← smul_pow' g alpha n, halpha, fixing_smul_unitInQbar]
    simp⟩

@[simp] theorem rootRatio_toMul (n : ℕ) [NeZero n] (a : (↥K)ˣ) (alpha : ℚbar2ˣ)
    (halpha : alpha ^ n = unitInQbar (K := K) a)
    (g : ↥(K.fixingSubgroup)) :
    (rootRatio n a alpha halpha g).toMul.1 = (g • alpha) * alpha⁻¹ := rfl

theorem rootRatio_continuous (n : ℕ) [NeZero n] (a : (↥K)ˣ) (alpha : ℚbar2ˣ)
    (halpha : alpha ^ n = unitInQbar (K := K) a) :
    Continuous (rootRatio n a alpha halpha : ↥(K.fixingSubgroup) → MuN n) := by
  refine IsLocallyConstant.continuous ?_
  rw [IsLocallyConstant.iff_exists_open]
  intro g
  let S : Set ↥(K.fixingSubgroup) := {h | h • alpha = alpha}
  have hS : IsOpen S := by
    have hfield : IsOpen {h : ↥(K.fixingSubgroup) | h.1 • (alpha : ℚbar2) = (alpha : ℚbar2)} :=
      (stabilizer_isOpen_of_isIntegral (K := ℚ_[2]) (alpha : ℚbar2)).preimage continuous_subtype_val
    convert hfield using 1
    ext h
    simp only [S, Set.mem_setOf_eq]
    constructor
    · intro hu
      exact congrArg Units.val hu
    · intro hv
      exact Units.ext hv
  let O : Set ↥(K.fixingSubgroup) := (fun h => g⁻¹ * h) ⁻¹' S
  have hO : IsOpen O := hS.preimage (continuous_const.mul continuous_id)
  have hgO : g ∈ O := by
    change g⁻¹ * g ∈ S
    simp [S]
  refine ⟨O, hO, hgO, fun h hh => ?_⟩
  have hhfix : (g⁻¹ * h) • alpha = alpha := hh
  have hha : h • alpha = g • alpha := by
    calc
      h • alpha = (g * (g⁻¹ * h)) • alpha := by rw [mul_inv_cancel_left]
      _ = g • ((g⁻¹ * h) • alpha) := mul_smul _ _ _
      _ = g • alpha := congrArg (g • ·) hhfix
  apply Additive.toMul.injective
  apply Subtype.ext
  simp only [rootRatio_toMul]
  rw [hha]

theorem rootRatio_cocycle (n : ℕ) [NeZero n] (a : (↥K)ˣ) (alpha : ℚbar2ˣ)
    (halpha : alpha ^ n = unitInQbar (K := K) a)
    (g h : ↥(K.fixingSubgroup)) :
    rootRatio n a alpha halpha (g * h) =
      rootRatio n a alpha halpha g + g • rootRatio n a alpha halpha h := by
  apply Additive.toMul.injective
  apply Subtype.ext
  change ((g * h) • alpha) * alpha⁻¹ =
    ((g • alpha) * alpha⁻¹) * (g • ((h • alpha) * alpha⁻¹))
  rw [mul_smul, smul_mul', smul_inv']
  calc
    (g • h • alpha) * alpha⁻¹ =
        ((g • alpha) * (g • alpha)⁻¹) * ((g • h • alpha) * alpha⁻¹) := by simp
    _ = (g • alpha) * alpha⁻¹ * ((g • h • alpha) * (g • alpha)⁻¹) := by
      ac_rfl

noncomputable def higherKummerCocycleOfRoot (n : ℕ) [NeZero n] (a : (↥K)ˣ)
    (alpha : ℚbar2ˣ) (halpha : alpha ^ n = unitInQbar (K := K) a) :
    Z1 ↥(K.fixingSubgroup) (MuN n) :=
  ⟨rootRatio n a alpha halpha,
    (mem_Z1_iff).2 ⟨rootRatio_continuous n a alpha halpha,
      rootRatio_cocycle n a alpha halpha⟩⟩

noncomputable def higherKummerCocycle (n : ℕ) [NeZero n] (a : (↥K)ˣ) :
    Z1 ↥(K.fixingSubgroup) (MuN n) :=
  higherKummerCocycleOfRoot n a (higherRootUnit n a) (higherRootUnit_pow n a)

noncomputable def higherKummerClass (n : ℕ) [NeZero n] (a : (↥K)ˣ) :
    H1 ↥(K.fixingSubgroup) (MuN n) :=
  H1mk _ _ (higherKummerCocycle n a)

def rootChange (n : ℕ) [NeZero n] (a : (↥K)ˣ)
    (alpha beta : ℚbar2ˣ)
    (halpha : alpha ^ n = unitInQbar (K := K) a)
    (hbeta : beta ^ n = unitInQbar (K := K) a) : MuN n := by
  let u : ℚbar2ˣ := alpha * beta⁻¹
  exact Additive.ofMul ⟨u, by
    rw [mem_rootsOfUnity, mul_pow, inv_pow, halpha, hbeta]
    simp⟩

@[simp] theorem rootChange_toMul (n : ℕ) [NeZero n] (a : (↥K)ˣ)
    (alpha beta : ℚbar2ˣ)
    (halpha : alpha ^ n = unitInQbar (K := K) a)
    (hbeta : beta ^ n = unitInQbar (K := K) a) :
    (rootChange n a alpha beta halpha hbeta).toMul.1 = alpha * beta⁻¹ := rfl

theorem rootRatio_sub_eq_dZero_rootChange (n : ℕ) [NeZero n] (a : (↥K)ˣ)
    (alpha beta : ℚbar2ˣ)
    (halpha : alpha ^ n = unitInQbar (K := K) a)
    (hbeta : beta ^ n = unitInQbar (K := K) a)
    (g : ↥(K.fixingSubgroup)) :
    rootRatio n a alpha halpha g - rootRatio n a beta hbeta g =
      dZero ↥(K.fixingSubgroup) (MuN n) (rootChange n a alpha beta halpha hbeta) g := by
  apply Additive.toMul.injective
  apply Subtype.ext
  change ((g • alpha) * alpha⁻¹) * ((g • beta) * beta⁻¹)⁻¹ =
    (g • (alpha * beta⁻¹)) * (alpha * beta⁻¹)⁻¹
  rw [smul_mul', smul_inv', mul_inv_rev, mul_inv_rev]
  simp only [inv_inv]
  simp only [mul_comm, mul_left_comm, mul_assoc]

theorem higherKummerClassOfRoot_eq (n : ℕ) [NeZero n] (a : (↥K)ˣ)
    (alpha : ℚbar2ˣ) (halpha : alpha ^ n = unitInQbar (K := K) a) :
    H1mk _ _ (higherKummerCocycleOfRoot n a alpha halpha) = higherKummerClass n a := by
  rw [higherKummerClass]
  change QuotientAddGroup.mk' _ (higherKummerCocycleOfRoot n a alpha halpha) =
    QuotientAddGroup.mk' _ (higherKummerCocycle n a)
  apply QuotientAddGroup.eq_iff_sub_mem.mpr
  rw [AddSubgroup.mem_addSubgroupOf]
  refine ⟨rootChange n a alpha (higherRootUnit n a) halpha (higherRootUnit_pow n a), ?_⟩
  funext g
  exact (rootRatio_sub_eq_dZero_rootChange n a alpha (higherRootUnit n a)
    halpha (higherRootUnit_pow n a) g).symm

@[simp] theorem unitInQbar_mul (a b : (↥K)ˣ) :
    unitInQbar (K := K) (a * b) = unitInQbar a * unitInQbar b := by
  simp [unitInQbar]

theorem rootRatio_mul (n : ℕ) [NeZero n] (a b : (↥K)ˣ)
    (alpha beta : ℚbar2ˣ)
    (halpha : alpha ^ n = unitInQbar (K := K) a)
    (hbeta : beta ^ n = unitInQbar (K := K) b)
    (g : ↥(K.fixingSubgroup)) :
    rootRatio n (a * b) (alpha * beta) (by rw [mul_pow, halpha, hbeta, unitInQbar_mul]) g =
      rootRatio n a alpha halpha g + rootRatio n b beta hbeta g := by
  apply Additive.toMul.injective
  apply Subtype.ext
  change (g • (alpha * beta)) * (alpha * beta)⁻¹ =
    ((g • alpha) * alpha⁻¹) * ((g • beta) * beta⁻¹)
  rw [smul_mul', mul_inv_rev]
  simp only [mul_comm, mul_left_comm, mul_assoc]

theorem higherKummerClass_mul (n : ℕ) [NeZero n] (a b : (↥K)ˣ) :
    higherKummerClass n (a * b) = higherKummerClass n a + higherKummerClass n b := by
  let alpha := higherRootUnit n a
  let beta := higherRootUnit n b
  have halpha : alpha ^ n = unitInQbar (K := K) a := higherRootUnit_pow n a
  have hbeta : beta ^ n = unitInQbar (K := K) b := higherRootUnit_pow n b
  have hab : (alpha * beta) ^ n = unitInQbar (K := K) (a * b) := by
    rw [mul_pow, halpha, hbeta, unitInQbar_mul]
  rw [← higherKummerClassOfRoot_eq n (a * b) (alpha * beta) hab,
    ← higherKummerClassOfRoot_eq n a alpha halpha,
    ← higherKummerClassOfRoot_eq n b beta hbeta,
    ← map_add]
  congr 1
  apply Subtype.ext
  funext g
  exact rootRatio_mul n a b alpha beta halpha hbeta g

theorem higherKummerClass_one (n : ℕ) [NeZero n] :
    higherKummerClass (K := K) n 1 = 0 := by
  have h := higherKummerClass_mul (K := K) n 1 1
  rw [one_mul] at h
  apply add_left_cancel (a := higherKummerClass (K := K) n 1)
  simpa using h.symm

noncomputable def higherKummerClassMonoidHom (n : ℕ) [NeZero n] :
    (↥K)ˣ →* Multiplicative (H1 ↥(K.fixingSubgroup) (MuN n)) where
  toFun a := Multiplicative.ofAdd (higherKummerClass n a)
  map_one' := congrArg Multiplicative.ofAdd (higherKummerClass_one (K := K) n)
  map_mul' a b := congrArg Multiplicative.ofAdd (higherKummerClass_mul n a b)

theorem higherKummerClass_eq_zero_iff (n : ℕ) [NeZero n] (a : (↥K)ˣ) :
    higherKummerClass n a = 0 ↔ ∃ b : (↥K)ˣ, b ^ n = a := by
  constructor
  · intro hzero
    rw [higherKummerClass] at hzero
    have hmem := (QuotientAddGroup.eq_zero_iff _).mp hzero
    rw [AddSubgroup.mem_addSubgroupOf] at hmem
    obtain ⟨xi, hxi⟩ := hmem
    let alpha := higherRootUnit n a
    let zeta : ℚbar2ˣ := xi.toMul.1
    let beta : ℚbar2ˣ := alpha * zeta⁻¹
    have hzeta_pow : zeta ^ n = 1 :=
      (mem_rootsOfUnity n (xi.toMul : ℚbar2ˣ)).mp xi.toMul.2
    have halpha_pow : alpha ^ n = unitInQbar (K := K) a := higherRootUnit_pow n a
    have hbeta_pow : beta ^ n = unitInQbar (K := K) a := by
      dsimp [beta]
      rw [mul_pow, inv_pow, halpha_pow, hzeta_pow, inv_one, mul_one]
    have hfix : ∀ g : ↥(K.fixingSubgroup), g • beta = beta := by
      intro g
      have hxi_g := congrFun hxi g
      have hmul := congrArg (fun t : MuN n => t.toMul.1) hxi_g
      change (g • zeta) * zeta⁻¹ = (g • alpha) * alpha⁻¹ at hmul
      have hga : g • alpha = (g • zeta) * zeta⁻¹ * alpha := by
        calc
          g • alpha = ((g • alpha) * alpha⁻¹) * alpha := by simp
          _ = ((g • zeta) * zeta⁻¹) * alpha := by rw [hmul]
      dsimp [beta]
      rw [smul_mul', smul_inv', hga]
      calc
        (g • zeta) * zeta⁻¹ * alpha * (g • zeta)⁻¹ =
            (g • zeta) * (g • zeta)⁻¹ * (alpha * zeta⁻¹) := by
          simp only [mul_comm, mul_left_comm, mul_assoc]
        _ = alpha * zeta⁻¹ := by simp
    have hfixed : (beta : ℚbar2) ∈ IntermediateField.fixedField K.fixingSubgroup := by
      rw [IntermediateField.mem_fixedField_iff]
      intro g hg
      have h := congrArg Units.val (hfix ⟨g, hg⟩)
      change g (beta : ℚbar2) = (beta : ℚbar2) at h
      exact h
    have hbetaK : (beta : ℚbar2) ∈ K := by
      rwa [InfiniteGalois.fixedField_fixingSubgroup K] at hfixed
    let b : ↥K := ⟨(beta : ℚbar2), hbetaK⟩
    have hb0 : b ≠ 0 := by
      intro hbzero
      exact beta.ne_zero (congrArg Subtype.val hbzero)
    refine ⟨Units.mk0 b hb0, ?_⟩
    apply Units.ext
    apply Subtype.ext
    exact congrArg Units.val hbeta_pow
  · rintro ⟨b, rfl⟩
    have hroot : (unitInQbar (K := K) b) ^ n = unitInQbar (K := K) (b ^ n) := by
      simp [unitInQbar]
    rw [← higherKummerClassOfRoot_eq n (b ^ n) (unitInQbar b) hroot]
    rw [← map_zero (H1mk ↥(K.fixingSubgroup) (MuN n))]
    congr 1
    apply Subtype.ext
    funext g
    apply Additive.toMul.injective
    apply Subtype.ext
    change (g • unitInQbar b) * (unitInQbar b)⁻¹ = 1
    rw [fixing_smul_unitInQbar]
    simp

theorem higherKummerClassMonoidHom_eq_one_iff (n : ℕ) [NeZero n] (a : (↥K)ˣ) :
    higherKummerClassMonoidHom (K := K) n a = 1 ↔
      ∃ b : (↥K)ˣ, b ^ n = a := by
  change Multiplicative.ofAdd (higherKummerClass n a) = 1 ↔ _
  change Multiplicative.ofAdd (higherKummerClass n a) = Multiplicative.ofAdd 0 ↔ _
  constructor
  · intro h
    exact (higherKummerClass_eq_zero_iff n a).mp (Multiplicative.ofAdd.injective h)
  · intro h
    exact congrArg Multiplicative.ofAdd ((higherKummerClass_eq_zero_iff n a).mpr h)

/-- The exact finite-image Hilbert-90 input needed at exponent `n`.  A `Z1` value already carries
continuity and the crossed-homomorphism law; coercion from `μ_n` to `ℚbar2ˣ` gives the
multiplicative cocycle trivialized here. -/
def MuNContinuousHilbert90 (K : IntermediateField ℚ_[2] ℚbar2)
    (n : ℕ) [NeZero n] : Prop :=
  ∀ z : Z1 ↥(K.fixingSubgroup) (MuN n),
    ∃ beta : ℚbar2ˣ, ∀ g,
      (z.1 g).toMul.1 = (g • beta) * beta⁻¹

theorem higherKummerClassMonoidHom_surjective_of_muNContinuousHilbert90
    (n : ℕ) [NeZero n] (hH90 : MuNContinuousHilbert90 K n) :
    Function.Surjective (higherKummerClassMonoidHom (K := K) n) := by
  intro y
  obtain ⟨z, hz⟩ := H1mk_surjective (G := ↥(K.fixingSubgroup))
    (M := MuN n) y.toAdd
  obtain ⟨beta, hbeta⟩ := hH90 z
  have hbetaPowFix : ∀ g : ↥(K.fixingSubgroup), g • (beta ^ n) = beta ^ n := by
    intro g
    have hfpow : ((z.1 g).toMul.1) ^ n = 1 :=
      (mem_rootsOfUnity n ((z.1 g).toMul : ℚbar2ˣ)).mp (z.1 g).toMul.2
    have hratioPow : ((g • beta) * beta⁻¹) ^ n = 1 := by
      rw [← hbeta g]
      exact hfpow
    rw [mul_pow, inv_pow, ← smul_pow'] at hratioPow
    exact mul_inv_eq_one.mp hratioPow
  have hfixed : ((beta ^ n : ℚbar2ˣ) : ℚbar2) ∈
      IntermediateField.fixedField K.fixingSubgroup := by
    rw [IntermediateField.mem_fixedField_iff]
    intro g hg
    have h := congrArg Units.val (hbetaPowFix ⟨g, hg⟩)
    change g ((beta ^ n : ℚbar2ˣ) : ℚbar2) = ((beta ^ n : ℚbar2ˣ) : ℚbar2) at h
    exact h
  have hbetaPowK : ((beta ^ n : ℚbar2ˣ) : ℚbar2) ∈ K := by
    rwa [InfiniteGalois.fixedField_fixingSubgroup K] at hfixed
  let a0 : ↥K := ⟨((beta ^ n : ℚbar2ˣ) : ℚbar2), hbetaPowK⟩
  have ha0 : a0 ≠ 0 := by
    intro hzero
    exact (beta ^ n).ne_zero (congrArg Subtype.val hzero)
  let a : (↥K)ˣ := Units.mk0 a0 ha0
  have hroot : beta ^ n = unitInQbar (K := K) a := by
    apply Units.ext
    rfl
  refine ⟨a, Multiplicative.toAdd.injective ?_⟩
  change higherKummerClass n a = y.toAdd
  rw [← higherKummerClassOfRoot_eq n a beta hroot, ← hz]
  congr 1
  apply Subtype.ext
  funext g
  apply Additive.toMul.injective
  apply Subtype.ext
  exact (hbeta g).symm

/-- The standard Kummer exact sequence follows from finite-image Hilbert 90 on `μ_n`, with no
Artin-map input.  This is the adapter consumed by the reciprocity layer. -/
noncomputable def higherKummerClassDataOfMuNContinuousHilbert90
    (n : ℕ) [NeZero n] (hH90 : MuNContinuousHilbert90 K n) :
    HigherKummerClassData K n where
  kummer := higherKummerClassMonoidHom n
  surjective := higherKummerClassMonoidHom_surjective_of_muNContinuousHilbert90 n hH90
  eq_one_iff := higherKummerClassMonoidHom_eq_one_iff n

/-! ## Exact regression to the existing mod-2 Kummer class -/

/-- At `n = 2`, the explicit root ratio, transported through the repository's coefficient
equivalence `μ₂ ≃ Z/2`, is exactly the existing sign-valued Kummer cocycle. -/
theorem muNTwoEquiv_rootRatio (a : (↥K)ˣ) (alpha : ℚbar2ˣ)
    (halpha : alpha ^ 2 = unitInQbar (K := K) a)
    (g : ↥(K.fixingSubgroup)) :
    LocalLiftingDuality.muNTwoEquiv (rootRatio 2 a alpha halpha g) =
      Kummer.kummerCocycleFun (alpha : ℚbar2) g.1 := by
  by_cases hfix : g • alpha = alpha
  · have hval : g.1 • (alpha : ℚbar2) = (alpha : ℚbar2) := congrArg Units.val hfix
    rw [Kummer.kummerCocycleFun_eq0 hval]
    rw [← map_zero LocalLiftingDuality.muNTwoEquiv]
    congr 1
    apply Additive.toMul.injective
    apply Subtype.ext
    change (g • alpha) * alpha⁻¹ = 1
    rw [hfix]
    simp
  · have hval : ¬g.1 • (alpha : ℚbar2) = (alpha : ℚbar2) := by
      intro h
      exact hfix (Units.ext h)
    rw [Kummer.kummerCocycleFun, if_neg hval]
    have hratio : rootRatio 2 a alpha halpha g ≠ 0 := by
      intro hzero
      have h := congrArg (fun x : MuN 2 => x.toMul.1) hzero
      change (g • alpha) * alpha⁻¹ = 1 at h
      exact hfix (mul_inv_eq_one.mp h)
    have himage : LocalLiftingDuality.muNTwoEquiv (rootRatio 2 a alpha halpha g) ≠ 0 := by
      intro hzero
      apply hratio
      apply LocalLiftingDuality.muNTwoEquiv.injective
      rw [hzero, map_zero]
    have key : ∀ x : ZMod 2, x ≠ 0 → x = 1 := by decide
    exact key _ himage

/-- **Class-level `n = 2` regression.**  The explicit higher Kummer class is exactly the
repository's existing `kummerClassK`, transported from `ZMod 2` to `μ₂`. -/
theorem higherKummerClass_two_eq_modTwoTransport (a : (↥K)ˣ) :
    higherKummerClass 2 a =
      H1congr (G := ↥(K.fixingSubgroup)) LocalLiftingDuality.muNTwoEquiv.symm
        (FieldData.muNTwoEquiv_symm_equivariant K) (kummerClassK K a) := by
  let alpha : ℚbar2ˣ := Units.mk0 (sqrtCl ((a : ↥K) : ℚbar2))
    (sqrtCl_ne_zero (unitCoe_ne_zero K a))
  have halpha : alpha ^ 2 = unitInQbar (K := K) a := by
    apply Units.ext
    exact sqrtCl_sq _
  rw [← higherKummerClassOfRoot_eq 2 a alpha halpha]
  unfold kummerClassK
  rw [H1congr_mk]
  congr 1
  apply Subtype.ext
  funext g
  change rootRatio 2 a alpha halpha g =
    LocalLiftingDuality.muNTwoEquiv.symm
      (Kummer.kummerCocycleFun (alpha : ℚbar2) g.1)
  apply LocalLiftingDuality.muNTwoEquiv.injective
  rw [LocalLiftingDuality.muNTwoEquiv.apply_symm_apply]
  exact muNTwoEquiv_rootRatio a alpha halpha g

/-- The explicit higher Kummer homomorphism at `n = 2` is the homomorphism already stored in
`modTwoHigherKummerClassData`. -/
theorem higherKummerClassMonoidHom_two_eq_modTwoHigherKummerClassData :
    higherKummerClassMonoidHom (K := K) 2 =
      (modTwoHigherKummerClassData (K := K)).kummer := by
  ext a
  apply Multiplicative.toAdd.injective
  exact higherKummerClass_two_eq_modTwoTransport a

/-- **Full package regression.**  Under finite-image Hilbert 90, the constructed `n = 2` Kummer
data equals the repository's pre-existing mod-2 data.  The proof fields agree by proof
irrelevance once the Kummer homomorphisms have been identified. -/
theorem higherKummerClassDataOfMuNContinuousHilbert90_two_eq_modTwo
    (hH90 : MuNContinuousHilbert90 K 2) :
    higherKummerClassDataOfMuNContinuousHilbert90 2 hH90 =
      modTwoHigherKummerClassData (K := K) := by
  rw [HigherKummerClassData.mk.injEq]
  exact higherKummerClassMonoidHom_two_eq_modTwoHigherKummerClassData

#print axioms higherKummerClassOfRoot_eq
#print axioms higherKummerClass_eq_zero_iff
#print axioms higherKummerClassMonoidHom_surjective_of_muNContinuousHilbert90
#print axioms higherKummerClassDataOfMuNContinuousHilbert90
#print axioms higherKummerClass_two_eq_modTwoTransport
#print axioms higherKummerClassDataOfMuNContinuousHilbert90_two_eq_modTwo

end
end GQ2.Dyadic
