/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, and OpenAI Codex
-/
import GQ2.Dyadic.Instances.GammaRPWordNielsenElementary
import GQ2.Dyadic.Instances.FieldFamilyFlexibleCertificate

/-!
# Transporting a core presentation by a Nielsen transformation

An inverse word-substitution pair acts contravariantly on presentation words and
covariantly on alphabet markings.  This module proves that a pair fixing the tame letter
transports the complete `CorePresentation`: relation, universal lift, computation on the
marking, and uniqueness.  It also transports the target group along a continuous
equivalence and packages the result as flexible core leaves once the two normalized
unramified rows are supplied.

The construction is rank-generic and uses only the universal property of the free
profinite group.  It is the presentation bridge needed by the changed-word even-M route.
-/

namespace GQ2.Dyadic.Instances.GammaRPWordNielsen

noncomputable section

open GQ2 GQ2.Dyadic
open GQ2.Dyadic.Certificates.MProcyclic
open GQ2.Dyadic.Instances.GammaRPWordNielsenElementary

namespace PWordNielsenPair

/-- Push a marking forward through a word substitution. -/
def forwardMark {n : ℕ} (T : PWordNielsenPair n)
    {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [TotallyDisconnectedSpace G] (t : Marking n G) :
    Marking n G :=
  ⟨fun g => t.eval (T.forward g)⟩

/-- Pull a marking backward through the inverse word substitution. -/
def backwardMark {n : ℕ} (T : PWordNielsenPair n)
    {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [TotallyDisconnectedSpace G] (t : Marking n G) :
    Marking n G :=
  ⟨fun g => t.eval (T.backward g)⟩

@[simp] theorem forwardMark_apply {n : ℕ} (T : PWordNielsenPair n)
    {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [TotallyDisconnectedSpace G] (t : Marking n G)
    (g : Generator n) :
    T.forwardMark t g = t.eval (T.forward g) := rfl

@[simp] theorem backwardMark_apply {n : ℕ} (T : PWordNielsenPair n)
    {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [TotallyDisconnectedSpace G] (t : Marking n G)
    (g : Generator n) :
    T.backwardMark t g = t.eval (T.backward g) := rfl

theorem forwardMark_eval {n : ℕ} (T : PWordNielsenPair n)
    {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [TotallyDisconnectedSpace G] (t : Marking n G)
    (w : PWord (Generator n)) :
    (T.forwardMark t).eval w = t.eval (PWord.subst T.forward w) := by
  exact (PWord.eval_subst ⇑t T.forward w).symm

theorem backwardMark_eval {n : ℕ} (T : PWordNielsenPair n)
    {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [TotallyDisconnectedSpace G] (t : Marking n G)
    (w : PWord (Generator n)) :
    (T.backwardMark t).eval w = t.eval (PWord.subst T.backward w) := by
  exact (PWord.eval_subst ⇑t T.backward w).symm

theorem forwardMark_backwardMark {n : ℕ} (T : PWordNielsenPair n)
    {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [TotallyDisconnectedSpace G] (t : Marking n G) :
    T.forwardMark (T.backwardMark t) = t := by
  ext g
  rw [forwardMark_apply, backwardMark_eval]
  exact GQ2.Dyadic.Instances.GammaRPWordNielsenElementary.PWordNielsenPair.backward_forward_eval
    T t (.gen g)

theorem backwardMark_forwardMark {n : ℕ} (T : PWordNielsenPair n)
    {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [TotallyDisconnectedSpace G] (t : Marking n G) :
    T.backwardMark (T.forwardMark t) = t := by
  ext g
  rw [backwardMark_apply, forwardMark_eval]
  exact GQ2.Dyadic.Instances.GammaRPWordNielsenElementary.PWordNielsenPair.forward_backward_eval
    T t (.gen g)

end PWordNielsenPair

end

end GQ2.Dyadic.Instances.GammaRPWordNielsen

namespace GQ2.Dyadic.Count.CorePresentation

noncomputable section

open GQ2 GQ2.Dyadic
open GQ2.Dyadic.Instances.GammaRPWordNielsen
open GQ2.Dyadic.Instances.GammaRPWordNielsenElementary

/-- Transport a core presentation contravariantly across a tau-fixing Nielsen pair. -/
noncomputable def ofNielsen
    {n : ℕ} {R : PWord (Generator n)} {P : ProfiniteGrp}
    (C : CorePresentation n R P) (T : PWordNielsenPair n)
    (hforwardTau : T.forward .tau = .gen .tau)
    (hbackwardTau : T.backward .tau = .gen .tau) :
    CorePresentation n (PWord.subst T.backward R) P where
  isProP := C.isProP
  mark := T.forwardMark C.mark
  mark_tau := by
    change C.mark.eval (T.forward .tau) = 1
    rw [hforwardTau]
    exact C.mark_tau
  rel := by
    have hTau : (T.forwardMark C.mark).τ = 1 := by
      change C.mark.eval (T.forward .tau) = 1
      rw [hforwardTau]
      exact C.mark_tau
    rw [Marking.eval_pro2 _ hTau
      (zpowHat_omega2_eq_self_of_isProP C.isProP)]
    rw [T.forwardMark_eval]
    rw [GQ2.Dyadic.Instances.GammaRPWordNielsenElementary.PWordNielsenPair.forward_backward_eval]
    rw [← Marking.eval_pro2 C.mark C.mark_tau
      (zpowHat_omega2_eq_self_of_isProP C.isProP)]
    exact C.rel
  liftHom := fun hQ t hTau hrel =>
    C.liftHom hQ (T.backwardMark t)
      (by
        change t.eval (T.backward .tau) = 1
        rw [hbackwardTau]
        exact hTau)
      (by
        have hBackTau : (T.backwardMark t).τ = 1 := by
          change t.eval (T.backward .tau) = 1
          rw [hbackwardTau]
          exact hTau
        rw [Marking.eval_pro2 _ hBackTau
          (zpowHat_omega2_eq_self_of_isProP hQ)]
        rw [T.backwardMark_eval]
        rw [← Marking.eval_pro2 t hTau
          (zpowHat_omega2_eq_self_of_isProP hQ)]
        exact hrel)
  liftHom_mark := by
    intro Q _ _ _ _ _ _ hQ t hTau hrel g
    rw [PWordNielsenPair.forwardMark_apply, Marking.map_eval]
    have hmark :
        (C.mark.map ⇑(C.liftHom hQ (T.backwardMark t)
          (by
            change t.eval (T.backward .tau) = 1
            rw [hbackwardTau]
            exact hTau)
          (by
            have hBackTau : (T.backwardMark t).τ = 1 := by
              change t.eval (T.backward .tau) = 1
              rw [hbackwardTau]
              exact hTau
            rw [Marking.eval_pro2 _ hBackTau
              (zpowHat_omega2_eq_self_of_isProP hQ)]
            rw [T.backwardMark_eval]
            rw [← Marking.eval_pro2 t hTau
              (zpowHat_omega2_eq_self_of_isProP hQ)]
            exact hrel))) = T.backwardMark t := by
      ext a
      exact C.liftHom_mark hQ _ _ _ a
    rw [hmark, T.backwardMark_eval]
    exact GQ2.Dyadic.Instances.GammaRPWordNielsenElementary.PWordNielsenPair.backward_forward_eval
      T t (.gen g)
  hom_ext := by
    intro A _ _ _ _ _ _ φ ψ h
    apply C.hom_ext φ ψ
    intro g
    have hmark : T.backwardMark (T.forwardMark C.mark) = C.mark :=
      T.backwardMark_forwardMark C.mark
    calc
      φ (C.mark g) = φ ((T.backwardMark (T.forwardMark C.mark)) g) := by
        rw [hmark]
      _ = φ ((T.forwardMark C.mark).eval (T.backward g)) := rfl
      _ = ((T.forwardMark C.mark).map ⇑φ).eval (T.backward g) :=
        Marking.map_eval φ _ _
      _ = ((T.forwardMark C.mark).map ⇑ψ).eval (T.backward g) := by
        congr 1
        exact Marking.ext fun a => h a
      _ = ψ ((T.forwardMark C.mark).eval (T.backward g)) :=
        (Marking.map_eval ψ _ _).symm
      _ = ψ ((T.backwardMark (T.forwardMark C.mark)) g) := rfl
      _ = ψ (C.mark g) := by rw [hmark]

/-- Transport the target of a core presentation through a continuous group equivalence. -/
noncomputable def mapEquiv
    {n : ℕ} {R : PWord (Generator n)} {P Q : ProfiniteGrp}
    (C : CorePresentation n R P) (hQ : IsProP 2 (Q : Type))
    (e : ContinuousMulEquiv (P : Type) (Q : Type)) :
    CorePresentation n R Q where
  isProP := hQ
  mark := C.mark.map ⇑e
  mark_tau := by rw [Marking.map_τ, C.mark_tau, map_one]
  rel := by
    change (C.mark.map ⇑(e : ContinuousMonoidHom (P : Type) (Q : Type))).eval
      (pro2 R) = 1
    calc
      (C.mark.map ⇑(e : ContinuousMonoidHom (P : Type) (Q : Type))).eval
          (pro2 R) = e (C.mark.eval (pro2 R)) :=
        (Marking.map_eval
          (e : ContinuousMonoidHom (P : Type) (Q : Type)) C.mark _).symm
      _ = 1 := by rw [C.rel, map_one]
  liftHom := fun hA t hTau hrel =>
    (C.liftHom hA t hTau hrel).comp
      (e.symm : ContinuousMonoidHom (Q : Type) (P : Type))
  liftHom_mark := by
    intro A _ _ _ _ _ _ hA t hTau hrel g
    change C.liftHom hA t hTau hrel (e.symm (e (C.mark g))) = t g
    rw [e.symm_apply_apply]
    exact C.liftHom_mark hA t hTau hrel g
  hom_ext := by
    intro A _ _ _ _ _ _ φ ψ h
    apply ContinuousMonoidHom.ext
    intro x
    obtain ⟨y, rfl⟩ := e.surjective x
    let eh : ContinuousMonoidHom (P : Type) (Q : Type) := e
    have heq : φ.comp eh = ψ.comp eh := by
      apply C.hom_ext
      intro g
      exact h g
    exact DFunLike.congr_fun heq y

#print axioms ofNielsen
#print axioms mapEquiv

end

end GQ2.Dyadic.Count.CorePresentation

namespace GQ2.Dyadic.Instances.FieldFamilyFlexibleCertificate.FlexibleCoreLeavesRN

noncomputable section

open GQ2 GQ2.Dyadic GQ2.Dyadic.Count
open GQ2.Dyadic.Instances.GammaRPWordNielsen

/-- Package a Nielsen-transported presentation once its normalized rows are known. -/
noncomputable def ofNielsen
    {n : ℕ} {R : PWord (Generator n)} {P : ProfiniteGrp}
    {nuP : ContinuousMonoidHom P Ztwo}
    (C : FlexibleCoreLeavesRN n R P nuP) (T : PWordNielsenPair n)
    (hforwardTau : T.forward .tau = .gen .tau)
    (hbackwardTau : T.backward .tau = .gen .tau)
    (hSigma : nuP (T.forwardMark C.presentation.mark .sigma) = ztwoOne)
    (hWild : ∀ j : Fin (n + 1),
      nuP (T.forwardMark C.presentation.mark (.wild j)) = 1) :
    FlexibleCoreLeavesRN n (PWord.subst T.backward R) P nuP where
  presentation := C.presentation.ofNielsen T hforwardTau hbackwardTau
  nu_sigma := hSigma
  nu_wild := hWild

/-- Change the alphabet and the presented target group in one step. -/
noncomputable def ofNielsenEquiv
    {n : ℕ} {R : PWord (Generator n)} {P Q : ProfiniteGrp}
    {nuQ : ContinuousMonoidHom Q Ztwo}
    (C : CorePresentation n R P) (T : PWordNielsenPair n)
    (hforwardTau : T.forward .tau = .gen .tau)
    (hbackwardTau : T.backward .tau = .gen .tau)
    (hQ : IsProP 2 (Q : Type))
    (e : ContinuousMulEquiv (P : Type) (Q : Type))
    (hSigma : nuQ (e (T.forwardMark C.mark .sigma)) = ztwoOne)
    (hWild : ∀ j : Fin (n + 1),
      nuQ (e (T.forwardMark C.mark (.wild j))) = 1) :
    FlexibleCoreLeavesRN n (PWord.subst T.backward R) Q nuQ where
  presentation := (C.ofNielsen T hforwardTau hbackwardTau).mapEquiv hQ e
  nu_sigma := hSigma
  nu_wild := hWild

#print axioms ofNielsen
#print axioms ofNielsenEquiv

end

end GQ2.Dyadic.Instances.FieldFamilyFlexibleCertificate.FlexibleCoreLeavesRN
