/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, and OpenAI Codex
-/
import GQ2.Dyadic.Instances.TameInertiaPrimeToTwo

/-!
# Prime-to-two tame correction of an arbitrary word

This is the Stokes-compatible refinement of `tameCorrectedWord`.  Under the honest even
residue-cardinality hypotheses it chooses a `tqTau` exponent with trivial maximal pro-`2`
component, then appends the inverse power to the word.  It preserves ordinary tame
specialization and every complete pro-`2` presentation exactly as the unrestricted correction
does, while additionally carrying the exponent datum needed by mod-two endpoint arguments.
-/

namespace GQ2.Dyadic

noncomputable section

open GQ2
open GQ2.Dyadic.Count

/-- A prime-to-two profinite exponent representing the tame defect of `R`. -/
noncomputable def tamePrimeToTwoCorrectionExponent {n q : ℕ}
    (hq0 : q ≠ 0) (hqe : Even q) (R : PWord (Generator n))
    (hR : (tameMarking n q).eval R ∈ inertiaPartQ q) : Zhat :=
  Classical.choose
    (exists_primeToTwoExponent_tqTau_of_mem_inertiaPartQ hq0 hqe hR)

theorem tamePrimeToTwoCorrectionExponent_spec {n q : ℕ}
    (hq0 : q ≠ 0) (hqe : Even q) (R : PWord (Generator n))
    (hR : (tameMarking n q).eval R ∈ inertiaPartQ q) :
    (tqTau q) ^ᶻ tamePrimeToTwoCorrectionExponent hq0 hqe R hR =
      (tameMarking n q).eval R :=
  (Classical.choose_spec
    (exists_primeToTwoExponent_tqTau_of_mem_inertiaPartQ hq0 hqe hR)).1

theorem maxProPMk_tamePrimeToTwoCorrectionExponent {n q : ℕ}
    (hq0 : q ≠ 0) (hqe : Even q) (R : PWord (Generator n))
    (hR : (tameMarking n q).eval R ∈ inertiaPartQ q) :
    maxProPMk 2 Zhat (tamePrimeToTwoCorrectionExponent hq0 hqe R hR) = 1 :=
  (Classical.choose_spec
    (exists_primeToTwoExponent_tqTau_of_mem_inertiaPartQ hq0 hqe hR)).2

/-- Append the inverse prime-to-two tame defect. -/
noncomputable def tamePrimeToTwoCorrectedWord {n q : ℕ}
    (hq0 : q ≠ 0) (hqe : Even q) (R : PWord (Generator n))
    (hR : (tameMarking n q).eval R ∈ inertiaPartQ q) :
    PWord (Generator n) :=
  .mul R (.inv (.profPow (.gen .tau)
    (tamePrimeToTwoCorrectionExponent hq0 hqe R hR)))

theorem tamePrimeToTwoCorrectedWord_specializes {n q : ℕ}
    (hq0 : q ≠ 0) (hqe : Even q) (R : PWord (Generator n))
    (hR : (tameMarking n q).eval R ∈ inertiaPartQ q) :
    TameSpec.TameSpecializes n q
      (tamePrimeToTwoCorrectedWord hq0 hqe R hR) := by
  rw [TameSpec.tameSpecializes_iff]
  simp only [tamePrimeToTwoCorrectedWord, Marking.eval_def, PWord.eval_mul,
    PWord.eval_inv, PWord.eval_profPow, PWord.eval_gen]
  rw [show (tameMarking n q) .tau = tqTau q from rfl,
    tamePrimeToTwoCorrectionExponent_spec]
  exact mul_inv_cancel _

theorem eval_pro2_tamePrimeToTwoCorrectedWord {n q : ℕ}
    (hq0 : q ≠ 0) (hqe : Even q) (R : PWord (Generator n))
    (hR : (tameMarking n q).eval R ∈ inertiaPartQ q)
    {Q : Type} [Group Q] [TopologicalSpace Q] [IsTopologicalGroup Q]
    [CompactSpace Q] [T2Space Q] [TotallyDisconnectedSpace Q]
    (hQ : IsProP 2 Q) (t : Marking n Q) (hTau : t.τ = 1) :
    t.eval (pro2 (tamePrimeToTwoCorrectedWord hq0 hqe R hR)) =
      t.eval (pro2 R) := by
  calc
    t.eval (pro2 (tamePrimeToTwoCorrectedWord hq0 hqe R hR)) =
        t.eval (tamePrimeToTwoCorrectedWord hq0 hqe R hR) :=
      PWord.eval_pro2 _ hTau (zpowHat_omega2_eq_self_of_isProP hQ) _
    _ = t.eval R := by
      rw [tamePrimeToTwoCorrectedWord, Marking.eval_def, PWord.eval_mul,
        PWord.eval_inv, PWord.eval_profPow, PWord.eval_gen]
      have hTau' : t .tau = 1 := hTau
      rw [hTau']
      rw [zpowHat_eq_one_of_maxProPMk_eq_one hQ]
      · simp only [inv_one, mul_one]
        rfl
      · exact maxProPMk_tamePrimeToTwoCorrectionExponent hq0 hqe R hR
    _ = t.eval (pro2 R) :=
      (PWord.eval_pro2 _ hTau (zpowHat_omega2_eq_self_of_isProP hQ) R).symm

namespace CorePresentation

/-- Prime-to-two correction preserves a complete pro-`2` presentation. -/
noncomputable def ofPrimeToTwoTameCorrection {n q : ℕ} {R : PWord (Generator n)}
    {P : ProfiniteGrp} (C : CorePresentation n R P)
    (hq0 : q ≠ 0) (hqe : Even q)
    (hR : (tameMarking n q).eval R ∈ inertiaPartQ q) :
    CorePresentation n (tamePrimeToTwoCorrectedWord hq0 hqe R hR) P where
  isProP := C.isProP
  mark := C.mark
  mark_tau := C.mark_tau
  rel := (eval_pro2_tamePrimeToTwoCorrectedWord
    hq0 hqe R hR C.isProP C.mark C.mark_tau).trans C.rel
  liftHom hQ t hTau hrel := by
    have hrel' : t.eval (pro2 R) = 1 :=
      (eval_pro2_tamePrimeToTwoCorrectedWord
        hq0 hqe R hR hQ t hTau).symm.trans hrel
    exact C.liftHom hQ t hTau hrel'
  liftHom_mark hQ t hTau hrel g := by
    have hrel' : t.eval (pro2 R) = 1 :=
      (eval_pro2_tamePrimeToTwoCorrectedWord
        hq0 hqe R hR hQ t hTau).symm.trans hrel
    exact C.liftHom_mark hQ t hTau hrel' g
  hom_ext := C.hom_ext

end CorePresentation

#print axioms tamePrimeToTwoCorrectionExponent_spec
#print axioms maxProPMk_tamePrimeToTwoCorrectionExponent
#print axioms tamePrimeToTwoCorrectedWord_specializes
#print axioms eval_pro2_tamePrimeToTwoCorrectedWord
#print axioms CorePresentation.ofPrimeToTwoTameCorrection

end

end GQ2.Dyadic
