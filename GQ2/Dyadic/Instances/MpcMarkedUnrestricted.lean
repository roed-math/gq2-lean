/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using OpenAI Codex
-/
import GQ2.Dyadic.Instances.MpcMarkedObstructions
import GQ2.Dyadic.Instances.StageAbstractionEvenDerivKer

/-!
# Unrestricted four-slot corrections for the marked Mpc successor

The first three coordinates of `mpcMkFiveNecessaryKernel` already characterize the
unrestricted four-slot depth correction.  This module makes that statement precise.  It
constructs the canonical even derivation family, transports its raw shift space across the
depth-two changes in the `B̄` and `D̄` base words, and identifies an unrestricted raw shift
exactly with `levelMk (mpcBldIncr t n us ut um un)` for four arbitrary depth-`r` inputs.

This is deliberately not the missing marked reflection theorem.  The final result consumes
the three crossed-derivation conjuncts of `mpcMkFiveNecessaryKernel`; the `nu` and `chi`
conjuncts are not needed until one asks to replace the four unrestricted inputs by the marked
carriers `mpcSxKill r`, `mpcSxKill r`, `mpcMkPivotKill r`, and `mpcSxKill r`.  No theorem in
the current tree proves that carrier refinement, so this module does not identify the full
five-kernel with the marked cost range.

Declaration prefix `mpcMk` (namespace `GQ2.Dyadic.Instances.MpcMk`).  No `sorry`, no new
axiom, no `native_decide`, and no heartbeat or recursion override.
-/

namespace GQ2.Dyadic.Instances.MpcMk

open GQ2 GQ2.Dyadic GQ2.Dyadic.MarkedCore Multiplicative
open GQ2.Dyadic.Instances.MpcWord GQ2.Dyadic.Instances.MpcBld
open GQ2.Dyadic.Instances.MpcLad GQ2.Dyadic.Instances.MpcSx
open GQ2.Roe.Labute GQ2.Dyadic.SqCore
open GQ2.Dyadic.StageGeneric GQ2.Dyadic.EvenFamily

noncomputable section

/-! ## 1. The canonical unrestricted raw shift space -/

private def mpcMkCanonicalTuple (k : ℕ) :
    Tuple (mStageWord 2 0 (by omega)) (vM 2)
      (DM 2 0 : Type) (chiM 2 0) k :=
  mTupleOfModel (G := (DM 2 0 : Type)) (chi := chiM 2 0)
    (by omega) (isProP_DM 2 0) (ContinuousMulEquiv.refl _)
    (fun _ ↦ rfl) k

private def mpcMkCanonicalFamily (k : ℕ) :
    EvenKernelDerivationFamily (mpcMkCanonicalTuple k) where
  lifts := dmGen 2 0
  lifts_chi := evenFam_chiM_dmGen 2 0
  lifts_level := fun _ ↦ rfl
  deriv := fun i _ ↦ mpcMkCoordinateDeriv (k + 1) (by omega) i
  deriv_base := fun i _ ↦ by
    exact evenFamDerivModelM_isChiShadow 2 0 (by omega) (by omega) (Pi.single i 1)
  deriv_diag := fun i _ ↦ by
    rw [mpcMkCoordinateDeriv, evenFamDerivModelM_u]
    rw [evenFam_two_dvd_iff_castHom_eq_zero (by omega)]
    norm_num
  deriv_off := fun i _ j _ hji ↦ by
    rw [mpcMkCoordinateDeriv, evenFamDerivModelM_u]
    simp only [Pi.single_apply]
    split_ifs with h
    · exact (hji h).elim
    · rw [map_zero]
      exact dvd_zero _

/-- The four base rows used by the unrestricted correction, in the target quotient. -/
def mpcMkRawBase (r : ℕ) (t n : (DM 2 0 : Type)) :
    Fin (coreRank 0) → levelQuot (DM 2 0 : Type) (r + 2) :=
  coreMark (h := 0)
    (levelMk (DM 2 0 : Type) (r + 2) (dmA 2 0))
    (levelMk (DM 2 0 : Type) (r + 2) (mpcWordLetB t))
    (levelMk (DM 2 0 : Type) (r + 2) (dmC 2 0))
    (levelMk (DM 2 0 : Type) (r + 2) (mpcWordLetD n))

private def mpcMkCanonicalBase (k : ℕ) :
    Fin (coreRank 0) → levelQuot (DM 2 0 : Type) (k + 1) :=
  fun i ↦ levelMk (DM 2 0 : Type) (k + 1) (dmGen 2 0 i)

private theorem mpcMk_rawBase_dbar_eq_canonical (r : ℕ)
    (t n : (DM 2 0 : Type))
    (ht : t ∈ twoCentralSeries (DM 2 0 : Type) 2)
    (hn : n ∈ twoCentralSeries (DM 2 0 : Type) 2)
    (V : EvenRawDepthCorrection (DM 2 0 : Type) 0 (r + 1)) :
    evenRawDbarWord (mpcMkRawBase r t n) V.correction =
      evenRawDbarWord (mpcMkCanonicalBase (r + 1)) V.correction := by
  let f := levelMk (DM 2 0 : Type) (r + 2)
  have hdrop : ∀ {a x e : levelQuot (DM 2 0 : Type) (r + 2)},
      a ∈ lambdaImage (DM 2 0 : Type) r (r + 2) →
      e ∈ lambdaImage (DM 2 0 : Type) 2 (r + 2) →
      commP a (x * e) = commP a x := by
    intro a x e ha he
    have hea : commP e a = 1 := mpcLad_vanish he ha
    have hae : commP a e = 1 := by rw [mpcSx_swap, hea, inv_one]
    rw [cfour_commP_mul_right,
      cfive_commP_zLayer_left (cfive_commP_mem_zLayer_left ha x) e,
      hae]
    simp only [one_mul, mul_one]
  have hB : mpcMkRawBase r t n 1 = mpcMkCanonicalBase (r + 1) 1 * f t := by
    change f (mpcWordLetB t) = f (dmGen 2 0 1) * f t
    rw [show dmGen 2 0 1 = dmB 2 0 from rfl, mpcWordLetB, map_mul]
  have hD : mpcMkRawBase r t n 3 = mpcMkCanonicalBase (r + 1) 3 * f n := by
    change f (mpcWordLetD n) = f (dmGen 2 0 3) * f n
    rw [show dmGen 2 0 3 = dmD 2 0 from rfl, mpcWordLetD, map_mul]
  have ht' : f t ∈ lambdaImage (DM 2 0 : Type) 2 (r + 2) := ⟨t, ht, rfl⟩
  have hn' : f n ∈ lambdaImage (DM 2 0 : Type) 2 (r + 2) := ⟨n, hn, rfl⟩
  rw [evenRawDbarWord, evenRawDbarWord]
  simp only [evenRawHandleDbarWord, List.finRange_zero, List.map_nil,
    List.prod_nil, mul_one, evenRawCoreDbarWord]
  rw [hB, hD, hdrop (V.depth 0) ht', hdrop (V.depth 2) hn']
  rfl

/-- The canonical raw shift space is unchanged when the `B̄` and `D̄` rows are modified by
depth-two inputs. -/
theorem mpcMk_canonicalRawShiftSpan_le_rawBase (r : ℕ)
    (hr : 2 ≤ r)
    (t n : (DM 2 0 : Type))
    (ht : t ∈ twoCentralSeries (DM 2 0 : Type) 2)
    (hn : n ∈ twoCentralSeries (DM 2 0 : Type) 2) :
    evenRawShiftSpan (mpcMkCanonicalBase (r + 1)) (by omega) ≤
      evenRawShiftSpan (mpcMkRawBase r t n) (by omega) := by
  rintro q ⟨z, ⟨V, hV⟩, hz⟩
  refine ⟨(evenRawDepthShiftHom (mpcMkRawBase r t n) (by omega)) V,
    ⟨V, rfl⟩, ?_⟩
  rw [← hz, ← hV]
  change evenRawDbarWord (mpcMkRawBase r t n) V.correction =
    evenRawDbarWord (mpcMkCanonicalBase (r + 1)) V.correction
  exact mpcMk_rawBase_dbar_eq_canonical r t n ht hn V

/-- Vanishing of the three non-twisted coordinate derivations places a top-layer class in
the canonical unrestricted raw shift space. -/
theorem mpcMk_mem_canonicalRawShiftSpan_of_threeKernels {k : ℕ} (hk : 3 ≤ k)
    {q : levelQuot (DM 2 0 : Type) (k + 1)}
    (hq : q ∈ zLayer (DM 2 0 : Type) k)
    (h0 : q ∈ derivKer (mpcMkCoordinateDeriv (k + 1) (by omega) 0) k)
    (h2 : q ∈ derivKer (mpcMkCoordinateDeriv (k + 1) (by omega) 2) k)
    (h3 : q ∈ derivKer (mpcMkCoordinateDeriv (k + 1) (by omega) 3) k) :
    q ∈ evenRawShiftSpan (mpcMkCanonicalBase k) hk := by
  let F := mpcMkCanonicalFamily k
  have hraw := evenDeriv_mem_rawShiftSpan_of_forall_derivKer
    (evenFam_isTopFinGen_DM 2 0) (isProP_DM 2 0) hk F
    (evenKernel_vM_sub_one_dvd_four (by omega))
    (evenKernel_vM_diagonal_add_one_dvd_four (α := 2) (h := 0)) hq
    (fun i hi ↦ by
      fin_cases i
      · simpa [F, mpcMkCanonicalFamily] using h0
      · exact (hi rfl).elim
      · simpa [F, mpcMkCanonicalFamily] using h2
      · simpa [F, mpcMkCanonicalFamily] using h3)
  obtain ⟨z, ⟨V, hV⟩, hz⟩ := hraw
  refine ⟨(evenRawDepthShiftHom (mpcMkCanonicalBase k) hk) V, ⟨V, rfl⟩, ?_⟩
  rw [← hz, ← hV]
  change evenRawDbarWord (mpcMkCanonicalBase k) V.correction =
    evenRawDbarWord
      (fun i ↦ canonLift (DM 2 0 : Type) k ((mpcMkCanonicalTuple k).generators i))
      V.correction
  symm
  exact F.evenDeriv_dbarWord_eq hk V.depth

/-- A class in the five necessary kernels has an unrestricted raw correction.  Only the
three crossed-derivation conjuncts are used here; `nu` and `chi` belong to the later marked
carrier refinement. -/
theorem mpcMk_mem_rawBase_of_fiveKernel {r : ℕ} (hr : 2 ≤ r)
    {t n : (DM 2 0 : Type)}
    (ht : t ∈ twoCentralSeries (DM 2 0 : Type) 2)
    (hn : n ∈ twoCentralSeries (DM 2 0 : Type) 2)
    {q : levelQuot (DM 2 0 : Type) (r + 2)}
    (hq : q ∈ zLayer (DM 2 0 : Type) (r + 1))
    (hfive : q ∈ mpcMkFiveNecessaryKernel (r + 1)) :
    q ∈ evenRawShiftSpan (mpcMkRawBase r t n) (by omega) := by
  obtain ⟨⟨⟨⟨h0, h2⟩, h3⟩, _⟩, _⟩ := hfive
  apply mpcMk_canonicalRawShiftSpan_le_rawBase r hr t n ht hn
  exact mpcMk_mem_canonicalRawShiftSpan_of_threeKernels (by omega) hq h0 h2 h3

/-! ## 2. Raw shifts are exactly unrestricted costs -/

/-- The raw depth correction represented by four unrestricted depth-`r` group elements. -/
def mpcMkRawCorrection (r : ℕ) (us ut um un : (DM 2 0 : Type))
    (hus : us ∈ twoCentralSeries (DM 2 0 : Type) r)
    (hut : ut ∈ twoCentralSeries (DM 2 0 : Type) r)
    (hum : um ∈ twoCentralSeries (DM 2 0 : Type) r)
    (hun : un ∈ twoCentralSeries (DM 2 0 : Type) r) :
    EvenRawDepthCorrection (DM 2 0 : Type) 0 (r + 1) where
  correction := coreMark (h := 0)
    (levelMk (DM 2 0 : Type) (r + 2) us)
    (levelMk (DM 2 0 : Type) (r + 2) ut)
    (levelMk (DM 2 0 : Type) (r + 2) um)
    (levelMk (DM 2 0 : Type) (r + 2) un)
  depth i := by
    fin_cases i
    · exact ⟨us, hus, rfl⟩
    · exact ⟨ut, hut, rfl⟩
    · exact ⟨um, hum, rfl⟩
    · exact ⟨un, hun, rfl⟩

private theorem mpcMk_rawDbar_eq (r : ℕ)
    (t n us ut um un : (DM 2 0 : Type))
    (hus : us ∈ twoCentralSeries (DM 2 0 : Type) r)
    (hut : ut ∈ twoCentralSeries (DM 2 0 : Type) r)
    (hum : um ∈ twoCentralSeries (DM 2 0 : Type) r)
    (hun : un ∈ twoCentralSeries (DM 2 0 : Type) r) :
    evenRawDbarWord (mpcMkRawBase r t n)
      (mpcMkRawCorrection r us ut um un hus hut hum hun).correction =
      levelMk (DM 2 0 : Type) (r + 2) us ^ 2 *
        commP (levelMk (DM 2 0 : Type) (r + 2) us)
          (levelMk (DM 2 0 : Type) (r + 2) (dmA 2 0)) *
        (commP (levelMk (DM 2 0 : Type) (r + 2) ut)
          (levelMk (DM 2 0 : Type) (r + 2) (dmA 2 0)) *
        commP (levelMk (DM 2 0 : Type) (r + 2) us)
          (levelMk (DM 2 0 : Type) (r + 2) (mpcWordLetB t))) *
        (commP (levelMk (DM 2 0 : Type) (r + 2) un)
          (levelMk (DM 2 0 : Type) (r + 2) (dmC 2 0)) *
        commP (levelMk (DM 2 0 : Type) (r + 2) um)
          (levelMk (DM 2 0 : Type) (r + 2) (mpcWordLetD n))) := by
  simp [evenRawDbarWord, evenRawCoreDbarWord, evenRawHandleDbarWord,
    mpcMkRawBase, mpcMkRawCorrection]

private theorem mpcMk_reorderRows {Q : Type*} [Group Q] (a b c d e f : Q)
    (hcd : Commute c d) (hef : Commute e f) (hcf : Commute c f) :
    a * b * (c * d) * (e * f) = a * b * d * f * c * e := by
  calc
    a * b * (c * d) * (e * f) = a * b * (d * c) * (f * e) := by
      rw [hcd.eq, hef.eq]
    _ = a * b * d * (c * f) * e := by group
    _ = a * b * d * (f * c) * e := by rw [hcf.eq]
    _ = a * b * d * f * c * e := by group

/-- The unrestricted raw shift represented by four depth-`r` inputs is exactly their
`mpcBldIncr` cost class. -/
theorem mpcMk_rawShift_eq_cost (r : ℕ) (hr : 2 ≤ r)
    (t n us ut um un : (DM 2 0 : Type))
    (hus : us ∈ twoCentralSeries (DM 2 0 : Type) r)
    (hut : ut ∈ twoCentralSeries (DM 2 0 : Type) r)
    (hum : um ∈ twoCentralSeries (DM 2 0 : Type) r)
    (hun : un ∈ twoCentralSeries (DM 2 0 : Type) r) :
    ((evenRawDepthShiftHom (mpcMkRawBase r t n) (by omega))
      (mpcMkRawCorrection r us ut um un hus hut hum hun)).1 =
      levelMk (DM 2 0 : Type) (r + 2)
        (mpcBldIncr t n us ut um un) := by
  let f := levelMk (DM 2 0 : Type) (r + 2)
  let S := f us ^ 2
  let UA := commP (f us) (f (dmA 2 0))
  let UB := commP (f us) (f (mpcWordLetB t))
  let TA := commP (f ut) (f (dmA 2 0))
  let MD := commP (f um) (f (mpcWordLetD n))
  let NC := commP (f un) (f (dmC 2 0))
  have hUs : f us ∈ lambdaImage (DM 2 0 : Type) r (r + 2) := ⟨us, hus, rfl⟩
  have hUt : f ut ∈ lambdaImage (DM 2 0 : Type) r (r + 2) := ⟨ut, hut, rfl⟩
  have hUm : f um ∈ lambdaImage (DM 2 0 : Type) r (r + 2) := ⟨um, hum, rfl⟩
  have hUn : f un ∈ lambdaImage (DM 2 0 : Type) r (r + 2) := ⟨un, hun, rfl⟩
  have hTA : TA ∈ zLayer (DM 2 0 : Type) (r + 1) := by
    exact commP_mem_zLayer (r + 1) (by omega) hUt _
  have hMD : MD ∈ zLayer (DM 2 0 : Type) (r + 1) := by
    exact commP_mem_zLayer (r + 1) (by omega) hUm _
  have hNC : NC ∈ zLayer (DM 2 0 : Type) (r + 1) := by
    exact commP_mem_zLayer (r + 1) (by omega) hUn _
  have hAT : commP (f (dmA 2 0)) (f ut) = TA := by
    rw [mpcSx_swap, show (commP (f ut) (f (dmA 2 0)))⁻¹ = TA from
      (zLayer_inv_self hTA).trans rfl]
  have hCN : commP (f (dmC 2 0)) (f un) = NC := by
    rw [mpcSx_swap, show (commP (f un) (f (dmC 2 0)))⁻¹ = NC from
      (zLayer_inv_self hNC).trans rfl]
  change evenRawDbarWord (mpcMkRawBase r t n)
      (mpcMkRawCorrection r us ut um un hus hut hum hun).correction = _
  rw [mpcMk_rawDbar_eq]
  change S * UA * (TA * UB) * (NC * MD) = _
  rw [show levelMk (DM 2 0 : Type) (r + 2) (mpcBldIncr t n us ut um un) =
    S * UA * UB * MD * TA * NC by
      simp [mpcBldIncr, f, S, UA, UB, MD, hAT, hCN,
        map_mul, map_pow, mpcBld_map_commP]]
  exact mpcMk_reorderRows S UA TA UB NC MD
    (zLayer_commute hTA UB) (zLayer_commute hNC MD) (zLayer_commute hTA MD)

/-- Membership in the unrestricted raw shift span is equivalent to an explicit four-slot
`mpcBldIncr` witness with all four inputs in depth `r`. -/
theorem mpcMk_mem_rawShiftSpan_iff_exists_unrestrictedCost
    (r : ℕ) (hr : 2 ≤ r) (t n : (DM 2 0 : Type))
    (q : levelQuot (DM 2 0 : Type) (r + 2)) :
    q ∈ evenRawShiftSpan (mpcMkRawBase r t n) (by omega) ↔
      ∃ us ut um un : (DM 2 0 : Type),
        us ∈ twoCentralSeries (DM 2 0 : Type) r ∧
        ut ∈ twoCentralSeries (DM 2 0 : Type) r ∧
        um ∈ twoCentralSeries (DM 2 0 : Type) r ∧
        un ∈ twoCentralSeries (DM 2 0 : Type) r ∧
        q = levelMk (DM 2 0 : Type) (r + 2)
          (mpcBldIncr t n us ut um un) := by
  constructor
  · rintro ⟨_, ⟨V, rfl⟩, rfl⟩
    obtain ⟨us, hus, huse⟩ := V.depth 0
    obtain ⟨ut, hut, hute⟩ := V.depth 1
    obtain ⟨um, hum, hume⟩ := V.depth 2
    obtain ⟨un, hun, hune⟩ := V.depth 3
    have hV : V = mpcMkRawCorrection r us ut um un hus hut hum hun := by
      ext i
      fin_cases i
      · exact huse.symm
      · exact hute.symm
      · exact hume.symm
      · exact hune.symm
    refine ⟨us, ut, um, un, hus, hut, hum, hun, ?_⟩
    rw [hV]
    exact mpcMk_rawShift_eq_cost r hr t n us ut um un hus hut hum hun
  · rintro ⟨us, ut, um, un, hus, hut, hum, hun, rfl⟩
    rw [← mpcMk_rawShift_eq_cost r hr t n us ut um un hus hut hum hun]
    exact evenRawDepthShift_mem_shiftSpan (mpcMkRawBase r t n) (by omega)
      (mpcMkRawCorrection r us ut um un hus hut hum hun)

/-- Every top-layer class in the five necessary kernels has an explicit unrestricted
four-slot cost witness.  Upgrading this witness to `MpcMkFullMove r` is the remaining marked
carrier-reflection theorem. -/
theorem mpcMk_exists_unrestrictedCost_of_fiveKernel {r : ℕ} (hr : 2 ≤ r)
    {t n : (DM 2 0 : Type)}
    (ht : t ∈ twoCentralSeries (DM 2 0 : Type) 2)
    (hn : n ∈ twoCentralSeries (DM 2 0 : Type) 2)
    {q : levelQuot (DM 2 0 : Type) (r + 2)}
    (hq : q ∈ zLayer (DM 2 0 : Type) (r + 1))
    (hfive : q ∈ mpcMkFiveNecessaryKernel (r + 1)) :
    ∃ us ut um un : (DM 2 0 : Type),
      us ∈ twoCentralSeries (DM 2 0 : Type) r ∧
      ut ∈ twoCentralSeries (DM 2 0 : Type) r ∧
      um ∈ twoCentralSeries (DM 2 0 : Type) r ∧
      un ∈ twoCentralSeries (DM 2 0 : Type) r ∧
      q = levelMk (DM 2 0 : Type) (r + 2)
        (mpcBldIncr t n us ut um un) := by
  exact (mpcMk_mem_rawShiftSpan_iff_exists_unrestrictedCost r hr t n q).mp
    (mpcMk_mem_rawBase_of_fiveKernel hr ht hn hq hfive)

/-! ## 3. Axiom pins

Every public declaration in this module is on the standard three
(`propext`, `Classical.choice`, `Quot.sound`).  This module introduces no axiom.
-/

#print axioms mpcMkRawBase
#print axioms mpcMk_canonicalRawShiftSpan_le_rawBase
#print axioms mpcMk_mem_canonicalRawShiftSpan_of_threeKernels
#print axioms mpcMk_mem_rawBase_of_fiveKernel
#print axioms mpcMkRawCorrection
#print axioms mpcMk_rawShift_eq_cost
#print axioms mpcMk_mem_rawShiftSpan_iff_exists_unrestrictedCost
#print axioms mpcMk_exists_unrestrictedCost_of_fiveKernel

end

end GQ2.Dyadic.Instances.MpcMk
