import GQ2.Dyadic.Instances.EvenModelCupForm
import GQ2.Dyadic.Instances.SqModelPresentingFrameCupAdapted
import GQ2.Dyadic.MarkedCore.N

/-! Transporting the actual DN presentation proves invariance of its mod-two cup form.
No orientation or coordinate-preservation premise is imposed on the automorphism. -/

namespace GQ2.Dyadic.Instances.DNAutomorphismCup

open Multiplicative GQ2.SectionThree GQ2.Dyadic.MarkedCore GQ2.Dyadic.EvenModel ContCoh

noncomputable section

local instance dnCupScalarAction (alpha h : Nat) :
    DistribMulAction (DN alpha h : Type) (ZMod 2) := scalarActionZmodTwo _

local instance dnCupContinuousScalar (alpha h : Nat) :
    ContinuousSMul (DN alpha h : Type) (ZMod 2) :=
  scalarActionZmodTwo_continuousSMul _

variable {alpha h : Nat}

theorem toZModPow_one_eq_nRed :
    (PadicInt.toZModPow (p := 2) 1 : ℤ_[2] →+* ZMod 2) = nRed := by
  apply ZMod.ringHom_eq_of_ker_eq
  rw [PadicInt.ker_toZModPow, nRed, PadicInt.ker_toZMod,
    PadicInt.maximalIdeal_eq_span_p, pow_one]

theorem continuous_nRed : Continuous (nRed : ℤ_[2] → ZMod 2) := by
  rw [← toZModPow_one_eq_nRed]
  rw [continuous_def]
  intro s _
  exact GQ2.isOpen_preimage_toZModPow 1 s

theorem markedRelator_dn_aut (halpha : 1 <= alpha)
    (Psi : ContinuousMulEquiv (DN alpha h : Type) (DN alpha h : Type)) :
    WordCoh.MarkedRelator (DN alpha h : Type) (nNatWord alpha h)
      (fun i => Psi (dnGen alpha h i)) := by
  refine { frattini := (markedRelator_DN alpha h halpha).frattini
           holds := by
             show nRelWord alpha (fun i => Psi (dnGen alpha h i)) = 1
             rw [<- map_nRelWord, dn_relation, map_one] }

noncomputable def presentedBy_dn_aut
    (Psi : ContinuousMulEquiv (DN alpha h : Type) (DN alpha h : Type)) :
    WordCoh.PresentedBy (DN alpha h : Type) (nNatWord alpha h)
      (fun i => Psi (dnGen alpha h i)) where
  liftHom hP nu hnu :=
    ((presentedBy_DN alpha h).liftHom hP nu hnu).comp
      <| { toMonoidHom := Psi.symm.toMonoidHom
           continuous_toFun := Psi.symm.continuous_toFun }
  liftHom_mark hP nu hnu k := by
    show (presentedBy_DN alpha h).liftHom hP nu hnu
      (Psi.symm (Psi (dnGen alpha h k))) = nu k
    rw [Psi.symm_apply_apply]
    exact (presentedBy_DN alpha h).liftHom_mark hP nu hnu k
  hom_ext phi psi hgen := by
    have hcomp :
        phi.comp { toMonoidHom := Psi.toMonoidHom
                   continuous_toFun := Psi.continuous_toFun } =
          psi.comp { toMonoidHom := Psi.toMonoidHom
                     continuous_toFun := Psi.continuous_toFun } :=
      (presentedBy_DN alpha h).hom_ext _ _ hgen
    refine DFunLike.ext _ _ fun x => ?_
    have hx := DFunLike.congr_fun hcomp (Psi.symm x)
    change phi (Psi (Psi.symm x)) = psi (Psi (Psi.symm x)) at hx
    rwa [Psi.apply_symm_apply] at hx

noncomputable def dnAutObs (halpha : 1 <= alpha)
    (Psi : ContinuousMulEquiv (DN alpha h : Type) (DN alpha h : Type)) :
    H2 (DN alpha h : Type) (ZMod 2) →+ ZMod 2 :=
  WordCoh.obsH2 (fun _ _ => rfl) (nNatWord alpha h)
    (fun i => Psi (dnGen alpha h i)) (markedRelator_dn_aut halpha Psi)

theorem dnAutObs_injective (halpha : 1 <= alpha)
    (Psi : ContinuousMulEquiv (DN alpha h : Type) (DN alpha h : Type)) :
    Function.Injective (dnAutObs halpha Psi) :=
  WordCoh.obsH2_injective (fun _ _ => rfl) (nNatWord alpha h)
    (fun i => Psi (dnGen alpha h i)) (markedRelator_dn_aut halpha Psi)
    (presentedBy_dn_aut Psi) (isProP_DN alpha h)

theorem dnObs_eq_dnAutObs (halpha : 1 <= alpha)
    (Psi : ContinuousMulEquiv (DN alpha h : Type) (DN alpha h : Type)) :
    dnObs alpha h halpha = dnAutObs halpha Psi :=
  GQ2.Dyadic.LSquare.addMonoidHom_zmodTwo_eq_of_injective _ _
    (dnObs_injective alpha h halpha) (dnAutObs_injective halpha Psi)

theorem evenCupForm_comp_dn_aut (halpha : 2 <= alpha)
    (Psi : ContinuousMulEquiv (DN alpha h : Type) (DN alpha h : Type))
    (c d : ContinuousMonoidHom (DN alpha h : Type) (Multiplicative (ZMod 2))) :
    evenCupForm
        (fun i => toAdd ((c.comp (autHom Psi)) (dnGen alpha h i)))
        (fun i => toAdd ((d.comp (autHom Psi)) (dnGen alpha h i))) =
      evenCupForm (fun i => toAdd (c (dnGen alpha h i)))
        (fun i => toAdd (d (dnGen alpha h i))) := by
  have ha1 : 1 <= alpha := by omega
  have hPsi := obsH2_evenModel_nNatWord_characterCup
    (G := (DN alpha h : Type)) (fun _ _ => rfl) alpha h halpha
    (fun i => Psi (dnGen alpha h i)) (markedRelator_dn_aut ha1 Psi) c d
  have hid := dnFrattiniCupForm alpha h ha1 halpha c d
  have hobs : forall z, WordCoh.obsH2 (fun _ _ => rfl) (nNatWord alpha h)
      (fun i => Psi (dnGen alpha h i)) (markedRelator_dn_aut ha1 Psi) z =
        dnObs alpha h ha1 z := fun z =>
    congrArg (fun F : H2 (DN alpha h : Type) (ZMod 2) →+ ZMod 2 => F z)
      (dnObs_eq_dnAutObs ha1 Psi).symm
  exact hPsi.symm.trans ((hobs _).trans hid)

#print axioms markedRelator_dn_aut
#print axioms toZModPow_one_eq_nRed
#print axioms continuous_nRed
#print axioms presentedBy_dn_aut
#print axioms dnAutObs
#print axioms dnAutObs_injective
#print axioms dnObs_eq_dnAutObs
#print axioms evenCupForm_comp_dn_aut

end
end GQ2.Dyadic.Instances.DNAutomorphismCup
