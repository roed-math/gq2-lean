import GQ2.Dyadic.MarkedCore.NBasisFullFrameLift
import GQ2.Dyadic.MarkedCore.NFrameCupCoordinates

/-!
# Lifting the full N-frame orientation/cup stabilizer

Every continuous automorphism of the actual full N abelian frame preserving
the canonical orientation and mod-two cup form lifts to an actual continuous
automorphism of D_N. Handles may mix arbitrarily. The conclusion is an
all-element commuting square, including the torsion coordinate.

The proof constructs the initial free basis, proves its literal depth-three
relator error from cup preservation, supplies every exact-row filtered stage,
and takes the torsion-sensitive compact limit. No stage-supply or hypothetical
group-lift premise remains.
-/

namespace GQ2.Dyadic.MarkedCore
noncomputable section
open GQ2 GQ2.SectionThree Multiplicative
open scoped GQ2.SectionThree.TopAbInstances

/-- The actual full abelian frame quotient of D_N. -/
def nCanonicalFrameHom {alpha : ℕ} (ha : 2 ≤ alpha) (h : ℕ) :
    ContinuousMonoidHom (DN alpha h : Type) (NFrameModel h) :=
  (⟨(nFrameExists_phiEquiv ha h).toMulEquiv.toMonoidHom,
    (nFrameExists_phiEquiv ha h).continuous_toFun⟩ : ContinuousMonoidHom _ _).comp
      ⟨abMk, continuous_abMk⟩

theorem nCanonicalFrameHom_apply {alpha : ℕ} (ha : 2 ≤ alpha) (h : ℕ)
    (x : DN alpha h) :
    nCanonicalFrameHom ha h x = nPhiHom ha h (abMk x) := rfl

theorem nCanonicalFrameHom_surjective {alpha : ℕ} (ha : 2 ≤ alpha) (h : ℕ) :
    Function.Surjective (nCanonicalFrameHom ha h) :=
  (nFrameExists_phiEquiv ha h).surjective.comp abMk_surjective

theorem nFrameOrientation_canonicalFrameHom {alpha : ℕ} (ha : 2 ≤ alpha) (h : ℕ)
    (x : DN alpha h) :
    nFrameOrientation ha h (nCanonicalFrameHom ha h x) = chiN alpha h x := by
  change abLiftG (chiN alpha h) ((nFrameExists_phiEquiv ha h).symm
    (nFrameExists_phiEquiv ha h (abMk x))) = _
  rw [ContinuousMulEquiv.symm_apply_apply, abLiftG_abMk]

/-- Full-frame stabilizer sufficiency, with no identity-handle restriction. -/
theorem nFullStabilizer_lift {alpha h : ℕ} (ha : 2 ≤ alpha)
    (phi : ContinuousMulEquiv (NFrameModel h) (NFrameModel h))
    (hchi : ∀ z, nFrameOrientation ha h (phi z) = nFrameOrientation ha h z)
    (hcup : NFrameCupIsometry ha phi) :
    ∃ Psi : ContinuousMulEquiv (DN alpha h : Type) (DN alpha h : Type),
      (∀ x, chiN alpha h (Psi x) = chiN alpha h x) ∧
      (∀ x, nPhiHom ha h (abMk (Psi x)) = phi (nPhiHom ha h (abMk x))) := by
  let e := nFrameLiftEquiv ha h phi
  have hhead := nFrameLiftEquiv_gen_zero ha h phi
  have herr := NInitialCupDepth.nRelWord_error_mem_three_of_cup alpha
    (fun i => e (freeTwoRankGen (coreRank h) i)) (freeTwoRankGen (coreRank h))
    hhead (nFrameLiftEquiv_cup hcup)
  obtain ⟨Psi, hPsi⟩ := exists_nFullFrameRealizes_of_headFixed_initialBasis ha e
    hhead (fun i => nFrameLiftEquiv_orientation ha h phi hchi _) herr
  refine ⟨Psi, hPsi.1, ?_⟩
  let P : ContinuousMonoidHom (DN alpha h : Type) (DN alpha h : Type) :=
    ⟨Psi.toMonoidHom, Psi.continuous_toFun⟩
  let F : ContinuousMonoidHom (NFrameModel h) (NFrameModel h) :=
    ⟨phi.toMonoidHom, phi.continuous_toFun⟩
  have heq : (nCanonicalFrameHom ha h).comp P = F.comp (nCanonicalFrameHom ha h) := by
    apply dn_hom_ext
    intro i
    change nPhiHom ha h (abMk (Psi (dnGen alpha h i))) =
      phi (nPhiHom ha h (abMk (dnGen alpha h i)))
    calc
      _ = freeNFrameProjection ha h (e (freeTwoRankGen (coreRank h) i)) := hPsi.2 i
      _ = phi (freeNFrameProjection ha h (freeTwoRankGen (coreRank h) i)) :=
        nFrameLiftEquiv_projection ha h phi _
      _ = _ := congrArg phi (freeNFrameProjection_gen ha h i)
  intro x
  exact DFunLike.congr_fun heq x

/-- The exact image condition, stated entirely on the full abelian frame.
This does not assert a finite explicit Nielsen-generator presentation. -/
theorem nFullStabilizer_lift_iff {alpha h : ℕ} (ha : 2 ≤ alpha)
    (phi : ContinuousMulEquiv (NFrameModel h) (NFrameModel h)) :
    (∃ Psi : ContinuousMulEquiv (DN alpha h : Type) (DN alpha h : Type),
      (∀ x, chiN alpha h (Psi x) = chiN alpha h x) ∧
      (∀ x, nPhiHom ha h (abMk (Psi x)) = phi (nPhiHom ha h (abMk x)))) ↔
    (∀ z, nFrameOrientation ha h (phi z) = nFrameOrientation ha h z) ∧
      NFrameCupIsometry ha phi := by
  constructor
  · rintro ⟨Psi, hchi, hframe⟩
    have hf (x : DN alpha h) :
        nCanonicalFrameHom ha h (Psi x) = phi (nCanonicalFrameHom ha h x) := hframe x
    constructor
    · intro z
      obtain ⟨x, rfl⟩ := nCanonicalFrameHom_surjective ha h z
      rw [← hf, nFrameOrientation_canonicalFrameHom,
        nFrameOrientation_canonicalFrameHom, hchi]
    · intro c d
      have hc := GQ2.Dyadic.Instances.DNAutomorphismCup.evenCupForm_comp_dn_aut ha Psi
        (c.comp (nCanonicalFrameHom ha h)) (d.comp (nCanonicalFrameHom ha h))
      change GQ2.Dyadic.EvenModel.evenCupForm
          (fun i => toAdd (c (nCanonicalFrameHom ha h (Psi (dnGen alpha h i)))))
          (fun i => toAdd (d (nCanonicalFrameHom ha h (Psi (dnGen alpha h i))))) =
        GQ2.Dyadic.EvenModel.evenCupForm
          (fun i => toAdd (c (nCanonicalFrameHom ha h (dnGen alpha h i))))
          (fun i => toAdd (d (nCanonicalFrameHom ha h (dnGen alpha h i)))) at hc
      simpa only [hf, nCanonicalFrameHom_apply, nFrameCanonicalMark] using hc
  · rintro ⟨hchi, hcup⟩
    exact nFullStabilizer_lift ha phi hchi hcup

#print axioms nCanonicalFrameHom
#print axioms nCanonicalFrameHom_apply
#print axioms nCanonicalFrameHom_surjective
#print axioms nFrameOrientation_canonicalFrameHom
#print axioms nFullStabilizer_lift
#print axioms nFullStabilizer_lift_iff

end
end GQ2.Dyadic.MarkedCore
