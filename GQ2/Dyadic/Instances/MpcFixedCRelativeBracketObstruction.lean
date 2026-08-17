/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using OpenAI Codex
-/
import GQ2.Dyadic.Instances.MpcOneHandleBalancedLimit
import GQ2.Dyadic.Instances.EvenStratumShift

/-!
# The square obstruction to fixed-C relative bracket surjectivity

`MpcOneHandleBalancedLimit.lean` isolated `FixedCRelativeBracketSurjective c` as a sufficient
rungwise input for one-handle defect absorption.  The input is too strong: it asks fixed-`C`
bracketing to cover the whole relative handle kernel.

Every rung contains an unavoidable square direction: `U₀^(2^j)` lies in
`λ_(j+1) ∩ ker(dmForgetHandles)`.  Every commutator `[c,epsilon]` is killed by every abelian
handle character, whereas the first handle coordinate modulo `2^(j+1)` detects this power
outside `λ_(j+2)`.  Thus `fixedC_handlePower_ne` gives an all-rung obstruction and
`not_fixedCRelativeBracketSurjective` proves the proposed input false for every `c`,
independently of any presentation or choice of lifts.

Balanced relator residuals do not contain this square direction: their complete abelian row is
zero.  `FixedCRelativeNeutralBracketSurjective` therefore restricts the target to relative
abelian-neutral layers.  `oneHandleDAbsorbable_of_balanced_fixedC_neutral` proves that this
restricted premise is still stable under the corrected-`D` climb and suffices for the exact
compactness consumer.  Hence the remaining honest graded seam is fixed-`C` surjectivity on the
abelian-neutral relative layer, not on the full handle kernel.
-/

namespace GQ2.Dyadic.Instances.MpcFixedCRelativeBracketObstruction

noncomputable section

open GQ2 GQ2.Dyadic Multiplicative
open GQ2.Dyadic.MarkedCore
open GQ2.Dyadic.SqCore
open GQ2.Dyadic.StageGeneric
open GQ2.Dyadic.Instances.MpcGeneralHandleStandardStabilization
open GQ2.Dyadic.Instances.MpcOneHandleDefectObstruction
open GQ2.Dyadic.Instances.MpcOneHandleBalancedLimit
open GQ2.Roe.Labute

/-- The first handle coordinate reduced modulo four. -/
def oneHandleUModFour :
    ContinuousMonoidHom (DM 2 1) (Multiplicative (ZMod 4)) where
  toMonoidHom :=
    (AddMonoidHom.toMultiplicative
      (PadicInt.toZModPow (p := 2) 2).toAddMonoidHom).comp oneHandleUChar.toMonoidHom
  continuous_toFun := by
    have hred : Continuous (PadicInt.toZModPow (p := 2) 2) := by
      rw [continuous_def]
      intro T _
      exact isOpen_preimage_toZModPow 2 T
    exact continuous_ofAdd.comp
      (hred.comp (continuous_toAdd.comp oneHandleUChar.continuous_toFun))

@[simp] theorem oneHandleUModFour_handleU :
    oneHandleUModFour (dmGen 2 1 (handleIdxU (0 : Fin 1))) =
      ofAdd (1 : ZMod 4) := by
  change ofAdd (PadicInt.toZModPow (p := 2) 2
    (toAdd (oneHandleUChar (dmGen 2 1 (handleIdxU (0 : Fin 1)))))) = _
  rw [oneHandleUChar_handleU, toAdd_ofAdd, map_one]

theorem oneHandleUModFour_pow_four (x : Multiplicative (ZMod 4)) : x ^ 4 = 1 := by
  obtain ⟨a, rfl⟩ : ∃ a : ZMod 4, ofAdd a = x := ⟨toAdd x, rfl⟩
  rw [← ofAdd_nsmul, nsmul_eq_mul, ZMod.natCast_self, zero_mul, ofAdd_zero]

/-- Reduction of the first handle coordinate modulo `2^k`. -/
def oneHandleUMod (k : ℕ) :
    ContinuousMonoidHom OneHandleGroup (Multiplicative (ZMod (2 ^ k))) where
  toMonoidHom :=
    (AddMonoidHom.toMultiplicative
      (PadicInt.toZModPow (p := 2) k).toAddMonoidHom).comp oneHandleUChar.toMonoidHom
  continuous_toFun := by
    have hred : Continuous (PadicInt.toZModPow (p := 2) k) := by
      rw [continuous_def]
      intro T _
      exact isOpen_preimage_toZModPow k T
    exact continuous_ofAdd.comp
      (hred.comp (continuous_toAdd.comp oneHandleUChar.continuous_toFun))

@[simp] theorem oneHandleUMod_handleU (k : ℕ) :
    oneHandleUMod k (dmGen 2 1 (handleIdxU (0 : Fin 1))) =
      ofAdd (1 : ZMod (2 ^ k)) := by
  change ofAdd (PadicInt.toZModPow k
    (toAdd (oneHandleUChar (dmGen 2 1 (handleIdxU (0 : Fin 1)))))) = _
  rw [oneHandleUChar_handleU, toAdd_ofAdd, map_one]

private theorem oneHandleUMod_pow_exp (k : ℕ)
    (x : Multiplicative (ZMod (2 ^ k))) : x ^ 2 ^ k = 1 := by
  obtain ⟨a, rfl⟩ : ∃ a : ZMod (2 ^ k), ofAdd a = x := ⟨toAdd x, rfl⟩
  rw [← ofAdd_nsmul, nsmul_eq_mul, ZMod.natCast_self, zero_mul, ofAdd_zero]

/-- The first-handle digit on the `(k+1)`-st two-central quotient. -/
def oneHandleULevel (k : ℕ) :
    levelQuot OneHandleGroup (k + 1) →* Multiplicative (ZMod (2 ^ k)) :=
  QuotientGroup.lift (twoCentralSeries OneHandleGroup (k + 1))
    (oneHandleUMod k).toMonoidHom (fun g hg => by
      have him : oneHandleUMod k g ∈
          twoCentralSeries (Multiplicative (ZMod (2 ^ k))) (k + 1) :=
        map_twoCentralSeries_le (oneHandleUMod k).toMonoidHom
          (oneHandleUMod k).continuous_toFun (k + 1) ⟨g, hg, rfl⟩
      obtain ⟨x, hx⟩ := evenStratumShift_twoCentralSeries_le_pow k him
      rw [MonoidHom.mem_ker]
      change oneHandleUMod k g = 1
      rw [← hx]
      exact oneHandleUMod_pow_exp k x)

@[simp] theorem oneHandleULevel_levelMk (k : ℕ) (g : OneHandleGroup) :
    oneHandleULevel k (levelMk OneHandleGroup (k + 1) g) = oneHandleUMod k g :=
  rfl

/-- Fixed-`C` bracketing misses the pure handle-power direction at every rung. -/
theorem fixedC_handlePower_ne (c epsilon : OneHandleGroup) (j : ℕ) :
    levelMk OneHandleGroup (j + 2) (commP c epsilon) ≠
      levelMk OneHandleGroup (j + 2)
        (dmGen 2 1 (handleIdxU (0 : Fin 1)) ^ (2 ^ j)) := by
  intro heq
  have heq' :
      levelMk OneHandleGroup ((j + 1) + 1) (commP c epsilon) =
        levelMk OneHandleGroup ((j + 1) + 1)
          (dmGen 2 1 (handleIdxU (0 : Fin 1)) ^ (2 ^ j)) := by
    simpa only [show (j + 1) + 1 = j + 2 by omega] using heq
  have hchar := congrArg (oneHandleULevel (j + 1)) heq'
  rw [oneHandleULevel_levelMk, oneHandleULevel_levelMk] at hchar
  change oneHandleUMod (j + 1) (commP c epsilon) =
    oneHandleUMod (j + 1)
      (dmGen 2 1 (handleIdxU (0 : Fin 1)) ^ (2 ^ j)) at hchar
  have hc : oneHandleUMod (j + 1) (commP c epsilon) = 1 := by
    change (oneHandleUMod (j + 1)).toMonoidHom (commP c epsilon) = 1
    exact map_commP_eq_one (oneHandleUMod (j + 1)).toMonoidHom c epsilon
  rw [hc, map_pow, oneHandleUMod_handleU] at hchar
  have hzero : ((2 ^ j : ℕ) : ZMod (2 ^ (j + 1))) = 0 := by
    have h := congrArg toAdd hchar.symm
    simpa [toAdd_pow, nsmul_eq_mul] using h
  have hdvd : 2 ^ (j + 1) ∣ 2 ^ j :=
    (ZMod.natCast_eq_zero_iff _ _).mp hzero
  have hle : 2 ^ (j + 1) ≤ 2 ^ j := Nat.le_of_dvd (pow_pos (by omega) _) hdvd
  rw [pow_succ] at hle
  nlinarith [pow_pos (by omega : 0 < (2 : ℕ)) j]

/-- The square of the first handle generator survives in the third two-central quotient under
its mod-four handle coordinate. -/
theorem handleU_sq_not_mem_twoCentralSeries_three :
    dmGen 2 1 (handleIdxU (0 : Fin 1)) ^ 2 ∉
      twoCentralSeries (DM 2 1) 3 := by
  intro hu
  have him : oneHandleUModFour (dmGen 2 1 (handleIdxU (0 : Fin 1)) ^ 2) ∈
      twoCentralSeries (Multiplicative (ZMod 4)) 3 :=
    map_twoCentralSeries_le oneHandleUModFour.toMonoidHom
      oneHandleUModFour.continuous_toFun 3 ⟨_, hu, rfl⟩
  obtain ⟨x, hx⟩ := evenStratumShift_twoCentralSeries_le_pow 2 him
  have hone : oneHandleUModFour (dmGen 2 1 (handleIdxU (0 : Fin 1)) ^ 2) = 1 := by
    rw [← hx]
    exact oneHandleUModFour_pow_four x
  have h := congrArg toAdd hone
  simp only [map_pow, oneHandleUModFour_handleU, toAdd_pow, toAdd_ofAdd,
    toAdd_one, nsmul_eq_mul] at h
  have h' : (2 : ZMod 4) = 0 := by simpa using h
  exact (by decide : (2 : ZMod 4) ≠ 0) h'

/-- Fixed-`C` bracketing cannot cover the whole relative handle kernel: the first rung already
misses the `U₀²` square direction, for every choice of `c`. -/
theorem not_fixedCRelativeBracketSurjective (c : DM 2 1) :
    ¬ FixedCRelativeBracketSurjective c := by
  intro Had
  let u := dmGen 2 1 (handleIdxU (0 : Fin 1))
  have hu2 : u ^ 2 ∈ twoCentralSeries (DM 2 1) 2 :=
    sq_mem_twoCentralSeries_succ (DM 2 1) (Subgroup.mem_top u)
  have hqu2 : dmForgetHandles 2 1 (u ^ 2) = 1 := by
    dsimp [u]
    rw [map_pow, dmForgetHandles_handleU, one_pow]
  obtain ⟨epsilon, _, _, had⟩ := Had 1 (u ^ 2) hu2 hqu2
  have had' : levelMk (DM 2 1) 3 (commP c epsilon) =
      levelMk (DM 2 1) 3 (u ^ 2) := by
    simpa only [show 1 + 2 = 3 by omega] using had
  have hdiff : u ^ 2 * (commP c epsilon)⁻¹ ∈
      twoCentralSeries (DM 2 1) 3 := by
    rw [lim_mem_twoCentralSeries_iff_levelMk, map_mul, map_inv, had', mul_inv_cancel]
  have hcomm : oneHandleUModFour (commP c epsilon) = 1 := by
    change oneHandleUModFour.toMonoidHom (commP c epsilon) = 1
    exact map_commP_eq_one oneHandleUModFour.toMonoidHom c epsilon
  have him := map_twoCentralSeries_le oneHandleUModFour.toMonoidHom
    oneHandleUModFour.continuous_toFun 3 ⟨_, hdiff, rfl⟩
  have hu2deep : oneHandleUModFour (u ^ 2) ∈
      twoCentralSeries (Multiplicative (ZMod 4)) 3 := by
    rw [map_mul, map_inv] at him
    change oneHandleUModFour (u ^ 2) * (oneHandleUModFour (commP c epsilon))⁻¹ ∈
      twoCentralSeries (Multiplicative (ZMod 4)) 3 at him
    rw [hcomm, inv_one, mul_one] at him
    exact him
  obtain ⟨x, hx⟩ := evenStratumShift_twoCentralSeries_le_pow 2 hu2deep
  have hone : oneHandleUModFour (u ^ 2) = 1 := by
    rw [← hx]
    exact oneHandleUModFour_pow_four x
  have h := congrArg toAdd hone
  dsimp [u] at h
  simp only [map_pow, oneHandleUModFour_handleU, toAdd_pow, toAdd_ofAdd,
    nsmul_eq_mul] at h
  have h' : (2 : ZMod 4) = 0 := by simpa using h
  exact (by decide : (2 : ZMod 4) ≠ 0) h'

/-! ## The sharp repair: restrict the target to abelian-neutral residuals -/

/-- The residual directions compatible with a balanced relation row. -/
def OneHandleAbelianNeutral (r : DM 2 1) : Prop :=
  ∀ f : ContinuousMonoidHom (DM 2 1) (Multiplicative ℤ_[2]), f r = 1

/-- Fixed-`C` bracket surjectivity only on relative, abelian-neutral layers.  The square
counterexample above is excluded, since its first handle coordinate is nonzero. -/
def FixedCRelativeNeutralBracketSurjective (c : DM 2 1) : Prop :=
  ∀ (j : ℕ) (r : DM 2 1),
    r ∈ twoCentralSeries (DM 2 1) (j + 1) →
    dmForgetHandles 2 1 r = 1 →
    OneHandleAbelianNeutral r →
    ∃ epsilon : DM 2 1,
      epsilon ∈ twoCentralSeries (DM 2 1) j ∧
      dmForgetHandles 2 1 epsilon = 1 ∧
      levelMk (DM 2 1) (j + 2) (commP c epsilon) =
        levelMk (DM 2 1) (j + 2) r

theorem oneHandleDTarget_char_eq_one
    (f : ContinuousMonoidHom (DM 2 1) (Multiplicative ℤ_[2])) :
    f oneHandleDTarget = 1 := by
  change f ((commP (dmGen 2 1 (handleIdxU (0 : Fin 1)))
    (dmGen 2 1 (handleIdxV (0 : Fin 1))))⁻¹) = 1
  rw [map_inv]
  have hcomm : f (commP (dmGen 2 1 (handleIdxU (0 : Fin 1)))
      (dmGen 2 1 (handleIdxV (0 : Fin 1)))) = 1 := by
    change f.toMonoidHom (commP (dmGen 2 1 (handleIdxU (0 : Fin 1)))
      (dmGen 2 1 (handleIdxV (0 : Fin 1)))) = 1
    exact map_commP_eq_one f.toMonoidHom _ _
  rw [hcomm, inv_one]

theorem mWord_char_independent_D
    (f : ContinuousMonoidHom (DM 2 1) (Multiplicative ℤ_[2]))
    (a b c d e : DM 2 1) :
    f (mWord 2 a b c e) = f (mWord 2 a b c d) := by
  rw [map_mWord, map_mWord, mWord_comm, mWord_comm]

/-- The W179 corrected-`D` climb only needs bracket surjectivity on abelian-neutral residuals,
provided the fixed core word has its necessary balanced abelian row. -/
theorem oneHandleDLetterApproxSet_succ_of_fixedC_neutral
    (a b c d e : DM 2 1) (j : ℕ)
    (hqword : dmForgetHandles 2 1 (mWord 2 a b c d) = 1)
    (hneutral : ∀ f : ContinuousMonoidHom (DM 2 1) (Multiplicative ℤ_[2]),
      f (mWord 2 a b c d) = 1)
    (he : e ∈ oneHandleDLetterApproxSet a b c d (j + 1))
    (Had : FixedCRelativeNeutralBracketSurjective c) :
    (oneHandleDLetterApproxSet a b c d (j + 2)).Nonempty := by
  let r := (mWord 2 a b c e)⁻¹ * oneHandleDTarget
  have hr : r ∈ twoCentralSeries (DM 2 1) (j + 1) := he.2
  have hqe : dmForgetHandles 2 1 (mWord 2 a b c e) = 1 := by
    rw [map_mWord] at hqword ⊢
    rw [he.1]
    exact hqword
  have hqt : dmForgetHandles 2 1 oneHandleDTarget = 1 := by
    simp only [oneHandleDTarget, map_inv, commP, map_mul, dmForgetHandles_handleU,
      dmForgetHandles_handleV, inv_one, mul_one]
  have hqr : dmForgetHandles 2 1 r = 1 := by
    dsimp [r]
    rw [map_mul, map_inv, hqe, hqt, inv_one, one_mul]
  have hrneutral : OneHandleAbelianNeutral r := by
    intro f
    dsimp [r]
    rw [map_mul, map_inv, mWord_char_independent_D f a b c d e,
      hneutral f, oneHandleDTarget_char_eq_one, inv_one, one_mul]
  obtain ⟨epsilon, hepsilon, hqepsilon, had⟩ := Had j r hr hqr hrneutral
  refine ⟨e * epsilon, ?_, ?_⟩
  · rw [map_mul, hqepsilon, mul_one, he.1]
  · rw [lim_mem_twoCentralSeries_iff_levelMk]
    have hinc :
        levelMk (DM 2 1) (j + 2) (mWord 2 a b c (e * epsilon)) =
          levelMk (DM 2 1) (j + 2) (mWord 2 a b c e * commP c epsilon) := by
      simpa only [map_mWord, map_mul, commP, map_inv] using
        (MpcBld.mpcBld_incr_near (G := DM 2 1)
          (C := levelMk (DM 2 1) (j + 2) c) (y := 1)
          (show levelMk (DM 2 1) (j + 2) c =
            levelMk (DM 2 1) (j + 2) c * 1 by simp)
          (Subgroup.one_mem (lambdaImage (DM 2 1) 2 (j + 2)))
          ⟨epsilon, hepsilon, rfl⟩)
    rw [map_mul, map_inv, hinc, map_mul, mul_inv_rev]
    have hrmap : levelMk (DM 2 1) (j + 2) r =
        (levelMk (DM 2 1) (j + 2) (mWord 2 a b c e))⁻¹ *
          levelMk (DM 2 1) (j + 2) oneHandleDTarget := by
      dsimp [r]
      rw [map_mul, map_inv]
    rw [had, hrmap]
    group

/-- A balanced seed plus neutral relative fixed-`C` surjectivity suffices for exact absorption.
This is the sharp stable replacement for the false all-kernel premise. -/
theorem oneHandleDAbsorbable_of_balanced_fixedC_neutral
    (a b c d : DM 2 1)
    (hqword : dmForgetHandles 2 1 (mWord 2 a b c d) = 1)
    (hneutral : ∀ f : ContinuousMonoidHom (DM 2 1) (Multiplicative ℤ_[2]),
      f (mWord 2 a b c d) = 1)
    (hbase : (mWord 2 a b c d)⁻¹ * oneHandleDTarget ∈
      twoCentralSeries (DM 2 1) 2)
    (Had : FixedCRelativeNeutralBracketSurjective c) :
    MpcOneHandleDAbsorbable a b c d := by
  apply oneHandleDAbsorbable_of_DLetter_forall_class
  intro k
  by_cases hk : k ≤ 2
  · exact ⟨d, rfl, twoCentralSeries_antitone (DM 2 1) hk hbase⟩
  · obtain ⟨n, rfl⟩ : ∃ n, k = n + 2 := ⟨k - 2, by omega⟩
    clear hk
    induction n with
    | zero => exact ⟨d, rfl, hbase⟩
    | succ n ih =>
      obtain ⟨e, he⟩ := ih
      exact oneHandleDLetterApproxSet_succ_of_fixedC_neutral
        a b c d e (n + 1) hqword hneutral he Had

#print axioms oneHandleUModFour
#print axioms oneHandleUMod
#print axioms oneHandleULevel
#print axioms fixedC_handlePower_ne
#print axioms handleU_sq_not_mem_twoCentralSeries_three
#print axioms not_fixedCRelativeBracketSurjective
#print axioms FixedCRelativeNeutralBracketSurjective
#print axioms oneHandleDAbsorbable_of_balanced_fixedC_neutral

end
end GQ2.Dyadic.Instances.MpcFixedCRelativeBracketObstruction
