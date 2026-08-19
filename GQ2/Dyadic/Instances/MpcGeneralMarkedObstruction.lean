/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu
-/
import GQ2.Dyadic.Instances.MpcGeneralMarkedSpan

/-!
# The uniform secondary obstruction

The additive `D` coordinate descends to every finite two-central quotient.  A marked-stage
defect has zero top `D` digit, and the marked finite shift range lies in the same kernel.
This is the general, parameterized obstruction which replaces class-by-class defect tests.
-/

namespace GQ2.Dyadic.Instances.MpcGeneralMarkedObstruction

noncomputable section

open GQ2 GQ2.Dyadic Multiplicative
open GQ2.Dyadic.MarkedCore
open GQ2.Dyadic.StageGeneric
open GQ2.Dyadic.Instances.MpcGeneralFiniteStages
open GQ2.Dyadic.Instances.MpcGeneralFiniteSpan
open GQ2.Dyadic.Instances.MpcGeneralMarkedStages
open GQ2.Dyadic.Instances.MpcGeneralMarkedSpan
open GQ2.Roe.Labute

/-- Reduction of the general additive `D` coordinate modulo `2^k`. -/
def mpcGeneralDeltaDMod (alpha h k : ℕ) :
    ContinuousMonoidHom (DM alpha h : Type) (Multiplicative (ZMod (2 ^ k))) where
  toMonoidHom :=
    (AddMonoidHom.toMultiplicative (PadicInt.toZModPow k).toAddMonoidHom).comp
      (mpcGeneralDeltaD alpha h).toMonoidHom
  continuous_toFun := by
    have hred : Continuous (PadicInt.toZModPow (p := 2) k) := by
      rw [continuous_def]
      intro T _
      exact isOpen_preimage_toZModPow k T
    exact continuous_ofAdd.comp
      (hred.comp (continuous_toAdd.comp
        (mpcGeneralDeltaD alpha h).continuous_toFun))

private theorem mpcGeneralDeltaDMod_pow (k : ℕ)
    (x : Multiplicative (ZMod (2 ^ k))) : x ^ 2 ^ k = 1 := by
  obtain ⟨a, rfl⟩ : ∃ a : ZMod (2 ^ k), Multiplicative.ofAdd a = x :=
    ⟨Multiplicative.toAdd x, rfl⟩
  rw [← ofAdd_nsmul, nsmul_eq_mul, ZMod.natCast_self, zero_mul, ofAdd_zero]

/-- The top general `D` digit on `Q_(k+1)`. -/
def mpcGeneralDeltaDLevel (alpha h k : ℕ) :
    levelQuot (DM alpha h) (k + 1) →* Multiplicative (ZMod (2 ^ k)) :=
  QuotientGroup.lift (twoCentralSeries (DM alpha h : Type) (k + 1))
    (mpcGeneralDeltaDMod alpha h k).toMonoidHom (fun g hg => by
      have him : mpcGeneralDeltaDMod alpha h k g ∈
          twoCentralSeries (Multiplicative (ZMod (2 ^ k))) (k + 1) :=
        map_twoCentralSeries_le (mpcGeneralDeltaDMod alpha h k).toMonoidHom
          (mpcGeneralDeltaDMod alpha h k).continuous_toFun (k + 1) ⟨g, hg, rfl⟩
      obtain ⟨x, hx⟩ := evenStratumShift_twoCentralSeries_le_pow k him
      rw [MonoidHom.mem_ker]
      change mpcGeneralDeltaDMod alpha h k g = 1
      rw [← hx]
      exact mpcGeneralDeltaDMod_pow k x)

@[simp] theorem mpcGeneralDeltaDLevel_levelMk (alpha h k : ℕ)
    (g : DM alpha h) :
    mpcGeneralDeltaDLevel alpha h k (levelMk (DM alpha h) (k + 1) g) =
      mpcGeneralDeltaDMod alpha h k g :=
  rfl

/-- The kernel of the top general `D` digit. -/
def mpcGeneralDeltaDKernel (alpha h k : ℕ) :
    Subgroup (levelQuot (DM alpha h) (k + 1)) :=
  (mpcGeneralDeltaDLevel alpha h k).ker

/-- Every marked-stage target has zero secondary digit. -/
theorem mpcGeneralLevelTarget_mem_deltaDKernel {alpha h k : ℕ}
    {m : Fin (coreRank h) → (DM alpha h : Type)}
    (hm : m ∈ mpcGeneralMarkedStage alpha h k) :
    (mpcGeneralLevelTarget hm.1).1 ∈ mpcGeneralDeltaDKernel alpha h k := by
  rw [mpcGeneralDeltaDKernel, MonoidHom.mem_ker]
  change mpcGeneralDeltaDLevel alpha h k
    ((levelMk (DM alpha h) (k + 1) (mRelWord alpha m))⁻¹) = 1
  rw [map_inv, mpcGeneralDeltaDLevel_levelMk,
    show mpcGeneralDeltaDMod alpha h k (mRelWord alpha m) = 1 by
      change ofAdd (PadicInt.toZModPow k
        (mpcGeneralDeltaD alpha h (mRelWord alpha m)).toAdd) = 1
      rw [mpcGeneralMarkedStage_rel_deltaD_eq_one hm]
      simp,
    inv_one]

/-- Every marked finite shift has zero secondary digit. -/
theorem mpcGeneralMarkedLevelShift_mem_deltaDKernel
    {alpha h k : ℕ} (m : Fin (coreRank h) → (DM alpha h : Type))
    (hk : 3 ≤ k) (E : MpcGeneralMarkedLevelCorrection alpha h k) :
    (mpcGeneralMarkedLevelShiftHom m k hk E).1 ∈
      mpcGeneralDeltaDKernel alpha h k := by
  rw [mpcGeneralDeltaDKernel, MonoidHom.mem_ker]
  obtain ⟨e, -, -, -, hdelta, he⟩ :=
    (mem_mpcGeneralMarkedCorrectionImage_iff_exists (E 0).1).mp (E 0).2
  have hzero : mpcGeneralDeltaDLevel alpha h k (E 0).1 = 1 := by
    rw [← he, mpcGeneralDeltaDLevel_levelMk]
    change ofAdd (PadicInt.toZModPow k
      (mpcGeneralDeltaD alpha h e).toAdd) = 1
    rw [hdelta rfl]
    simp
  change mpcGeneralDeltaDLevel alpha h k
    (evenRawDbarWord
      (fun i => levelMk (DM alpha h) (k + 1) (m i))
      (fun i => (E i).1)) = 1
  have hcomm (x y : levelQuot (DM alpha h) (k + 1)) :
      mpcGeneralDeltaDLevel alpha h k (commP x y) = 1 :=
    map_commP_eq_one (mpcGeneralDeltaDLevel alpha h k) x y
  have hhandle (j : Fin h) :
      mpcGeneralDeltaDLevel alpha h k
        (commP (E (handleIdxV j)).1
            (levelMk (DM alpha h) (k + 1) (m (handleIdxU j))) *
          commP (E (handleIdxU j)).1
            (levelMk (DM alpha h) (k + 1) (m (handleIdxV j)))) = 1 := by
    rw [map_mul, hcomm, hcomm, one_mul]
  simp [evenRawDbarWord, evenRawCoreDbarWord, evenRawHandleDbarWord,
    hcomm, hzero]
  rw [map_list_prod]
  rw [List.map_map]
  generalize List.finRange h = L
  induction L with
  | nil => rfl
  | cons j L ih =>
      rw [List.map_cons, List.prod_cons, Function.comp_apply, hhandle,
        one_mul]
      exact ih

/-- The full marked range is contained in the uniform secondary kernel. -/
theorem mpcGeneralMarkedLevelShift_range_le_deltaDKernel
    {alpha h k : ℕ} (m : Fin (coreRank h) → (DM alpha h : Type))
    (hk : 3 ≤ k) :
    (mpcGeneralMarkedLevelShiftHom m k hk).range ≤
      (mpcGeneralDeltaDKernel alpha h k).comap
        (zLayer (DM alpha h) k).subtype := by
  rintro _ ⟨E, rfl⟩
  exact mpcGeneralMarkedLevelShift_mem_deltaDKernel m hk E

end

end GQ2.Dyadic.Instances.MpcGeneralMarkedObstruction

section AxiomPins

open GQ2.Dyadic.Instances.MpcGeneralMarkedObstruction

#print axioms mpcGeneralDeltaDMod
#print axioms mpcGeneralDeltaDLevel
#print axioms mpcGeneralDeltaDKernel
#print axioms mpcGeneralLevelTarget_mem_deltaDKernel
#print axioms mpcGeneralMarkedLevelShift_mem_deltaDKernel
#print axioms mpcGeneralMarkedLevelShift_range_le_deltaDKernel

end AxiomPins
