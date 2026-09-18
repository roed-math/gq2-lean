/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, and OpenAI Codex
-/
import GQ2.Dyadic.Words.L
import GQ2.Dyadic.Words.N0
import GQ2.Dyadic.Words.Npc
import GQ2.Dyadic.SelectedEta

/-!
# Uniform denotation bridges for the existing L, N0 and displayed Npc factories

These additive theorems prove literal PWord equality for the existing RawWord
factories at every handle rank. They do not replace the factories, re-encode the
handle node, alter its ordering or association, or change any frozen hash or
fixture. The existing handleFactors interpreter is proved to agree with its
ordered finRange list by a generic list argument and alphabet range bounds.

The old per-fixture denotation lemmas remain untouched. Their historical
comments that the generic bridge was unavailable describe an earlier proof
frontier, not an obstruction in the current denotation semantics.

The raw Npc theorem is a syntax identity for all integer numerator/denominator
pairs; well-formedness still requires the existing oddness conditions. The
semantic unit theorem consumes an EXACT NpcDisplayFor, never just congruence.
No claim is made that every arbitrary external two-adic unit has such a finite
rational display. The selected-source display producer is separate.
-/

namespace GQ2.Dyadic.GeneralTemplateLN
noncomputable section
open GQ2 GQ2.Dyadic Words Export

private theorem range_eq_finRange (h : ℕ) :
    List.range h = (List.finRange h).map Fin.val := by
  apply List.ext_getElem
  · simp
  · intro i hi hj
    simp

/-- The existing handle expander agrees with its ordered finite-index list,
without changing the raw tree or its unexpanded handle node. -/
theorem handleFactors_of_generators {Gen : Type*}
    (c : DenoteCtx Gen) (start h : ℕ) (u v : Fin h → Gen)
    (hu : ∀ j : Fin h, c.handleGen (start+2*(j : ℕ))=some (u j))
    (hv : ∀ j : Fin h, c.handleGen (start+2*(j : ℕ)+1)=some (v j)) :
    handleFactors c start h = some ((List.finRange h).map
      (fun j => PWord.comm (.gen (u j)) (.gen (v j)))) := by
  rw [handleFactors, range_eq_finRange, List.mapM_map]
  have heq : (fun j : Fin h => do
      let a ← c.handleGen (start+2*(j : ℕ))
      let b ← c.handleGen (start+2*(j : ℕ)+1)
      pure (PWord.comm (.gen a) (.gen b))) =
      (fun j : Fin h => some (PWord.comm (.gen (u j)) (.gen (v j)))) := by
    funext j
    simp [hu j, hv j]
  simp only [Function.comp_def]
  rw [heq]
  exact List.mapM_pure

theorem handleFactors_even (h : ℕ) :
    handleFactors (Words.denoteCtx h) 3 h = some ((List.finRange h).map
      (fun j => PWord.comm (.gen (Words.handleU j)) (.gen (Words.handleV j)))) := by
  apply handleFactors_of_generators
  · intro j
    have hj := j.isLt
    simp [Words.denoteCtx, Words.wildGen, Words.handleU, show 3+2*(j:ℕ)<2*h+3 by omega]
  · intro j
    have hj := j.isLt
    simp [Words.denoteCtx, Words.wildGen, Words.handleV,
      show 3+2*(j:ℕ)+1<2*h+3 by omega]
    omega

theorem handleFactors_odd (h : ℕ) :
    handleFactors (LSq.denoteCtx h) 2 h = some ((List.finRange h).map
      (fun j => PWord.comm (.gen (LSq.handleU j)) (.gen (LSq.handleV j)))) := by
  apply handleFactors_of_generators
  · intro j
    have hj := j.isLt
    simp [LSq.denoteCtx, LSq.wildGen, LSq.handleU, show 2+2*(j:ℕ)<2*h+2 by omega]
  · intro j
    have hj := j.isLt
    simp [LSq.denoteCtx, LSq.wildGen, LSq.handleV,
      show 2+2*(j:ℕ)+1<2*h+2 by omega]
    omega

theorem denote_handles_even (h : ℕ) :
    denote (Words.denoteCtx h) (.hyperbolicHandles 3 (.int h)) = some (Words.handlesW h) := by
  simp only [denote, RawExp.eval, Int.natCast_nonneg, ↓reduceIte, Int.toNat_natCast,
    handleFactors_even, Option.map_some, Words.handlesW]

theorem denote_handles_odd (h : ℕ) :
    denote (LSq.denoteCtx h) (.hyperbolicHandles 2 (.int h)) = some (LSq.handlesW h) := by
  simp only [denote, RawExp.eval, Int.natCast_nonneg, ↓reduceIte, Int.toNat_natCast,
    handleFactors_odd, Option.map_some, LSq.handlesW]

/-- The existing compact-N raw factory denotes the exact semantic word at every rank. -/
theorem denote_rawNCompact (alpha h : ℕ) :
    denote (Words.denoteCtx h) (Words.rawNCompact alpha h) =
      some (Words.nCompactW alpha h) := by
  have hh := handleFactors_even h
  simp only [Words.denoteCtx] at hh
  simp [Words.rawNCompact, Words.nCompactW, denote, denoteList, RawExp.eval,
    hh, Words.handlesW, Words.denoteCtx, Words.genOfName,
    Words.wildGen, Words.coreLetter, PWord.omega2Pow,
    show 0<2*h+3 by omega, show 1<2*h+3 by omega, show 2<2*h+3 by omega]

/-- The existing rational-display Npc factory denotes its exact semantic word,
uniformly in alpha, level, handle rank, numerator and denominator. -/
theorem denote_rawNpc (alpha r h : ℕ) (num den : ℤ) :
    denote (Words.denoteCtx h) (Npc.rawNpc alpha r h num den) =
      some (Npc.npcW alpha r h ⟨num,den⟩) := by
  have hh := handleFactors_even h
  simp only [Words.denoteCtx] at hh
  simp [Npc.rawNpc, Npc.npcW, Npc.rawA, Npc.rawD, Npc.rawDeltaZero,
    Npc.aW, Npc.bW, Npc.deltaZeroW, Npc.dBlockW, Npc.eBlockW,
    denote, denoteList, RawExp.eval, RawSpec.toZhat,
    hh, Words.handlesW, Words.denoteCtx, Words.genOfName,
    Words.wildGen, Words.coreLetter, PWord.omega2Pow,
    show 0<2*h+3 by omega, show 1<2*h+3 by omega, show 2<2*h+3 by omega]

/-- The existing odd-degree L factory denotes its exact semantic word at every
handle rank, preserving the no-handle-node convention at rank zero. -/
theorem denote_rawLsq (h : ℕ) :
    denote (LSq.denoteCtx h) (LSq.rawLsq h) = some (LSq.lSqW h) := by
  cases h with
  | zero => rfl
  | succ k =>
    have hh := handleFactors_odd (k+1)
    simp only [LSq.denoteCtx] at hh
    simp [LSq.rawLsq, LSq.rawLsqCore, LSq.rawHandleTail,
      LSq.lSqW, LSq.lSqCore, LSq.handleTail, denote, denoteList, RawExp.eval,
      hh, LSq.handlesW, LSq.denoteCtx, LSq.genOfName, LSq.wildGen,
      LSq.coreLetter, sigma2W, PWord.omega2Pow, show (0 : ℤ) ≤ (k : ℤ)+1 by omega]

/-- An exact compatible display ties the old raw factory to the actual semantic
unit word. A congruence to the unit would not suffice for this literal equality. -/
theorem denote_rawNpc_display (alpha r h : ℕ) {eta : ℤ_[2]ˣ} (d : NpcDisplayFor eta) :
    denote (Words.denoteCtx h) (Npc.rawNpc alpha r h d.data.num d.data.den) =
      some (Npc.npcWUnit alpha r h eta) := by
  rw [Npc.npcWUnit_eq_display alpha r h d]
  exact denote_rawNpc alpha r h d.data.num d.data.den

/-- The same displayed raw tree meets the existing S1.1 well-formedness test. -/
theorem wf_rawNpc_display (alpha r h : ℕ) {eta : ℤ_[2]ˣ} (d : NpcDisplayFor eta) :
    (Npc.rawNpc alpha r h d.data.num d.data.den).wf = true :=
  Npc.wf_rawNpc alpha r h d.num_odd d.den_odd

#print axioms handleFactors_of_generators
#print axioms handleFactors_even
#print axioms handleFactors_odd
#print axioms denote_handles_even
#print axioms denote_handles_odd
#print axioms denote_rawNCompact
#print axioms denote_rawNpc
#print axioms denote_rawLsq
#print axioms denote_rawNpc_display
#print axioms wf_rawNpc_display

end
end GQ2.Dyadic.GeneralTemplateLN

