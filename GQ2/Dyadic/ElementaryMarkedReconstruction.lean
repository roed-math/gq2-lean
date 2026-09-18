/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using OpenAI Codex
-/
import GQ2.Dyadic.ScalarMarkedReconstruction

/-!
# Simultaneous preservation of every elementary core character

Finite generation makes the set of continuous F2-valued core characters finite.
Their joint evaluation is a single finite elementary decoration, so one
reconstructed equivalence preserves all of them at once. This does not identify
the full pro-two core map: higher Frattini coordinates remain a separate issue.
-/

namespace GQ2.Dyadic
noncomputable section
open GQ2

variable {n q : ℕ} {P : ProfiniteGrp} {hP : IsProP 2 P}
  {nuP : ContinuousMonoidHom P Ztwo} {SN : SourceNumerics n}

/-- A finitely generated source makes every finite-target core hom set finite. -/
theorem SourceDataRN.finite_coreHom (S : SourceDataRN n q P hP nuP SN)
    (E : Type) [Group E] [TopologicalSpace E] [DiscreteTopology E] [Finite E] :
    Finite (ContinuousMonoidHom P E) := by
  haveI : Finite (ContinuousMonoidHom S.Γ E) := finite_continuousMonoidHom S.tfg E
  apply Finite.of_injective (fun f : ContinuousMonoidHom P E => f.comp S.pro2)
  intro f g h
  ext p
  obtain ⟨x, rfl⟩ := S.pro2_surjective p
  exact DFunLike.congr_fun h x

/-- Joint evaluation by every continuous elementary scalar character. -/
def elementaryCoreEvaluation (P : ProfiniteGrp) :
    ContinuousMonoidHom P
      ((ContinuousMonoidHom P (Multiplicative (ZMod 2))) → Multiplicative (ZMod 2)) where
  toFun p chi := chi p
  map_one' := funext fun chi => chi.map_one
  map_mul' p r := funext fun chi => chi.map_mul p r
  continuous_toFun := continuous_pi fun chi => chi.continuous_toFun

/-- A single equivalence preserves tame, full unramified nu, and every elementary
core character simultaneously; the quantifiers are not interchanged. -/
theorem exists_tameElementaryNuCompatible_equiv_of_sourcesRN
    (S₁ S₂ : SourceDataRN n q P hP nuP SN)
    (hq0 : q ≠ 0) (hqe : Even q) (hnuP : Function.Surjective nuP)
    (htame₁ : Function.Surjective S₁.tame) (hwild₁ : IsProP 2 S₁.tame.toMonoidHom.ker)
    (htame₂ : Function.Surjective S₂.tame) (hwild₂ : IsProP 2 S₂.tame.toMonoidHom.ker) :
    ∃ e : ContinuousMulEquiv S₁.Γ S₂.Γ,
      (∀ x, S₂.tame (e x) = S₁.tame x) ∧
      (∀ chi : ContinuousMonoidHom P (Multiplicative (ZMod 2)), ∀ x,
        chi (S₂.pro2 (e x)) = chi (S₁.pro2 x)) ∧
      (∀ x, nuP (S₂.pro2 (e x)) = nuP (S₁.pro2 x)) := by
  letI : Finite (ContinuousMonoidHom P (Multiplicative (ZMod 2))) :=
    S₁.finite_coreHom _
  have hexp : ∀ v : (ContinuousMonoidHom P (Multiplicative (ZMod 2))) →
      Multiplicative (ZMod 2), v ^ 2 = 1 := by
    intro v
    ext chi
    change (2 : ℕ) • (v chi).toAdd = (0 : ZMod 2)
    exact ZModModule.char_nsmul_eq_zero 2 (v chi).toAdd
  obtain ⟨e, ht, hs, hnu⟩ := exists_tameScalarNuCompatible_equiv_of_sourcesRN
    S₁ S₂ hq0 hqe hnuP htame₁ hwild₁ htame₂ hwild₂ (elementaryCoreEvaluation P) hexp
  exact ⟨e, ht, (fun chi x => congrFun (hs x) chi), hnu⟩

#print axioms SourceDataRN.finite_coreHom
#print axioms elementaryCoreEvaluation
#print axioms exists_tameElementaryNuCompatible_equiv_of_sourcesRN

end
end GQ2.Dyadic
