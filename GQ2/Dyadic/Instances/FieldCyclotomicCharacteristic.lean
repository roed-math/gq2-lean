import GQ2.CharacteristicCharacter
import GQ2.Dyadic.Instances.NOrientationCharacteristic
import GQ2.Dyadic.Instances.SqOrientationCharacteristic
import GQ2.Dyadic.Instances.FieldFamilySpliceSourceComplete

/-!
# The field pro-2 cyclotomic character is characteristic

All three improved core families now have a characteristic canonical orientation. The existing
field classification supplies one oriented equivalence in the selected family. Transport gives
characteristicness of the actual descended cyclotomic character on `G_K(2)`.

This is uniform in every range-selected family and every rank. The field-facing endpoint
retains the campaign's genuine ramified-i hypothesis. It uses the established field orientation
producer and therefore reports its inherited arithmetic axioms explicitly.
-/

namespace GQ2.Dyadic.Instances.FieldCyclotomicCharacteristic

open GQ2 GQ2.Dyadic GQ2.Dyadic.MarkedCore
open GQ2.Dyadic.Instances.MOrientationCharacteristic
open GQ2.Dyadic.Instances.NOrientationCharacteristic
open GQ2.Dyadic.Instances.SqOrientationCharacteristic

noncomputable section

variable {R : LocalReciprocity}
  {K : IntermediateField ℚ_[2] (AlgebraicClosure ℚ_[2])} [FiniteDimensional ℚ_[2] K]
  [CompactSpace (GalK K)] [T2Space (GalK K)] [TotallyDisconnectedSpace (GalK K)]
  [CompactSpace AbsGalQ2] [TotallyDisconnectedSpace AbsGalQ2]

/-- Any genuine range-selected field branch has characteristic descended cyclotomic character. -/
theorem chiCycKTwo_characteristic_of_matchesRange
    (B : MarkedRecip R K) (FF : DyadicUnitFiltration K)
    (D : FiniteDyadicParameters K FF)
    {W : FamilyFieldBranchWitness D.params (B.fieldMarkedPair FF)}
    (S : FamilyFieldBranchSelection K D.params (B.fieldMarkedPair FF) W)
    (hmatch : W.MatchesCyclotomicRange) :
    IsCharacteristicCharacter (chiCycKTwo (K := K)) := by
  cases hb : S.branch with
  | L =>
      have hdeg : Module.finrank ℚ_[2] K = 2 * handleCount D.params .L + 1 := by
        have hd := S.degree_eq_field
        rw [hb] at hd
        exact hd.symm
      obtain ⟨f, horient, _, _⟩ := SqCore.gUni_supply B FF hdeg
      exact IsCharacteristicCharacter.of_equiv
        (chiG := SqCore.chiSq (handleCount D.params .L))
        (sqCoreOrientationCharacteristic_all) f horient
  | N0 alpha =>
      obtain ⟨e⟩ := orientedEquivN_of_familySelection_of_matchesRange_n0 B FF S hmatch hb
      have ha : 1 ≤ alpha := by
        have hv := S.valid
        rw [hb] at hv
        exact le_trans (by omega) hv
      exact IsCharacteristicCharacter.of_equiv
        (chiG := chiN alpha (handleCount D.params (.N0 alpha)))
        (nCoreOrientationCharacteristic_all ha) e.1 e.2
  | Npc alpha r eta =>
      obtain ⟨e⟩ := orientedEquivN_of_familySelection_of_matchesRange_npc B FF S hmatch hb
      have ha : 1 ≤ alpha := by
        have hv := S.valid
        rw [hb] at hv
        exact le_trans (by omega) hv.1
      exact IsCharacteristicCharacter.of_equiv
        (chiG := chiN alpha (handleCount D.params (.Npc alpha r eta)))
        (nCoreOrientationCharacteristic_all ha) e.1 e.2
  | M0 alpha =>
      obtain ⟨e⟩ := orientedEquivM_of_familySelection_of_matchesRange_m0 B FF S hmatch hb
      have ha : 1 ≤ alpha := by
        have hv := S.valid
        rw [hb] at hv
        exact le_trans (by omega) hv
      exact IsCharacteristicCharacter.of_equiv
        (chiG := chiM alpha (handleCount D.params (.M0 alpha)))
        (mCoreOrientationCharacteristic_all ha) e.1 e.2
  | Mpc alpha r epsilon eta =>
      obtain ⟨e⟩ := orientedEquivM_of_familySelection_of_matchesRange_mpc B FF S hmatch hb
      have ha : 1 ≤ alpha := by
        have hv := S.valid
        rw [hb] at hv
        exact le_trans (by omega) hv.1
      exact IsCharacteristicCharacter.of_equiv
        (chiG := chiM alpha (handleCount D.params (.Mpc alpha r epsilon eta)))
        (mCoreOrientationCharacteristic_all ha) e.1 e.2

/-- The range selector discharges every classification choice; only the established field
bundles and the original ramified-i scope remain. -/
theorem chiCycKTwo_characteristic_ramifiedI
    (B : MarkedRecip R K) (FF : DyadicUnitFiltration K)
    (D : FiniteDyadicParameters K FF) (RI : RamifiedIData K) :
    IsCharacteristicCharacter (chiCycKTwo (K := K)) :=
  chiCycKTwo_characteristic_of_matchesRange B FF D
    (selectFieldBranchFamilyFromRange B FF D RI)
    (fieldFamilyWitnessFromRange_matchesCyclotomicRange B FF D RI)

#print axioms chiCycKTwo_characteristic_of_matchesRange
#print axioms chiCycKTwo_characteristic_ramifiedI

end

end GQ2.Dyadic.Instances.FieldCyclotomicCharacteristic
