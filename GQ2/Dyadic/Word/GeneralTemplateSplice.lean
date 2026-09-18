/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, and OpenAI Codex
-/
import GQ2.Dyadic.Word.GeneralTemplateM
import GQ2.Dyadic.Instances.EvenMHeadHandlePairSpliceSupply
import GQ2.Dyadic.Instances.MpcMobileNuSource

/-!
# STAGED exact bridges to the actual certified splice sources

The parameter `k[i]` is the full two-adic wild normalization coefficient;
`eta[0]` is the full mobile unit; `correction` is exactly the classically chosen
profinite exponent in the certified word. These bindings, not an arbitrary
numerical assignment, connect the serialized tree to the source certificate.
-/

namespace GQ2.Dyadic.GeneralTemplate

open GQ2 GQ2.Dyadic.MarkedCore
open Instances.GammaRCorePresentationNuNormalize
open Instances.EvenMHeadHandlePairCore Instances.EvenMHeadHandlePairNormalize
open Instances.EvenMHeadHandlePairSpliceSupply
open Instances.MProcyclicCore Instances.MpcMobileNuSource

/-- Bind all continuous parameters exactly. Unused parameter names are irrelevant
to the source trees; out-of-alphabet indices default to zero. -/
noncomputable def sourceEnvironment {n : ℕ} (k : Fin (n + 1) → ℤ_[2])
    (eta : ℤ_[2]) (correction : Zhat) : Environment where
  padic := fun name i => if name = "eta" then eta
    else if hi : i < n + 1 then k ⟨i, hi⟩ else 0
  profinite := fun _ => correction

@[simp] theorem sourceEnvironment_k {n : ℕ} (k : Fin (n + 1) → ℤ_[2])
    (eta : ℤ_[2]) (correction : Zhat) (i : Fin (n + 1)) :
    (sourceEnvironment k eta correction).padic "k" i.val = k i := by
  dsimp only [sourceEnvironment]
  rw [if_neg (by decide : "k" ≠ "eta"), dif_pos i.isLt]

@[simp] theorem sourceEnvironment_eta {n : ℕ} (k : Fin (n + 1) → ℤ_[2])
    (eta : ℤ_[2]) (correction : Zhat) :
    (sourceEnvironment k eta correction).padic "eta" 0 = eta := by
  simp [sourceEnvironment]

/-- All wild shear coefficients are named two-adic parameters. -/
def shearSubst {n : ℕ} : Generator n → Tree (Generator n)
  | .sigma => .gen .sigma
  | .tau => .gen .tau
  | .wild i => .mul (.gen (.wild i))
      (.profPow (.gen .sigma) (.padicOmega (.parameter "k" i.val)))

def shear {n : ℕ} (w : Tree (Generator n)) : Tree (Generator n) :=
  w.subst shearSubst

def correct {n : ℕ} (w : Tree (Generator n)) : Tree (Generator n) :=
  .mul w (.inv (.profPow (.gen .tau) (.parameter "correction")))

@[simp] theorem denote_shear {n : ℕ} (k : Fin (n + 1) → ℤ_[2])
    (eta : ℤ_[2]) (correction : Zhat) (w : Tree (Generator n)) :
    (shear w).denote (sourceEnvironment k eta correction) =
      PWord.subst (wildShearBackward k) (w.denote (sourceEnvironment k eta correction)) := by
  rw [shear, Tree.denote_subst]
  congr 1
  funext g
  cases g with
  | sigma => rfl
  | tau => rfl
  | wild i =>
      simp [shearSubst, Tree.denote, ProfiniteTerm.denote, PadicTerm.denote,
        sourceEnvironment_k, wildShearBackward]

@[simp] theorem denote_correct {n : ℕ} (k : Fin (n + 1) → ℤ_[2])
    (eta : ℤ_[2]) (correction : Zhat) (w : Tree (Generator n)) :
    (correct w).denote (sourceEnvironment k eta correction) =
      .mul (w.denote (sourceEnvironment k eta correction))
        (.inv (.profPow (.gen .tau) correction)) := rfl

/-- The actual pair source template, with every substitution expanded in the tree. -/
def pairSplice (alpha : ℕ) {h : ℕ} (j : Fin h) : Tree (Generator (2 + 2 * h)) :=
  splice (correct (shear (rawPair alpha j))) (compactM alpha h)

/-- The actual mobile source template, with arbitrary semantic eta. -/
def mobileSplice (alpha r p h : ℕ) : Tree (Generator (2 + 2 * h)) :=
  splice (correct (shear (rawMobile alpha r p h))) (compactM alpha h)

/-- Exact bindings selected by the normalized pair source, including its tame defect. -/
noncomputable def pairEnvironment (alpha h q : ℕ) (halpha : 1 ≤ alpha)
    (hq0 : q ≠ 0) (hqe : Even q) (j : Fin h)
    (nuP : ContinuousMonoidHom (DM alpha h : Type) Ztwo) : Environment :=
  sourceEnvironment
    (wildNuCoefficient nuP (headHandlePairCorePresentation alpha h halpha j).mark) 1
    (tamePrimeToTwoCorrectionExponent hq0 hqe
      (headHandlePairNormalizedW alpha h halpha j nuP)
      (tame_eval_headHandlePairNormalized_mem_inertia (q := q) halpha j nuP))

/-- The staged pair tree denotes the exact certified word, at every rank and every
continuous character. This is literal `PWord` equality, not evaluation equivalence. -/
theorem denote_pairSplice (alpha h q : ℕ) (halpha : 1 ≤ alpha)
    (hq0 : q ≠ 0) (hqe : Even q) (j : Fin h)
    (nuP : ContinuousMonoidHom (DM alpha h : Type) Ztwo) :
    (pairSplice alpha j).denote (pairEnvironment alpha h q halpha hq0 hqe j nuP) =
      headHandlePairSpliceW alpha h q halpha hq0 hqe j nuP := by
  simp only [pairSplice, denote_splice, pairEnvironment, denote_correct,
    denote_shear, denote_rawPair, denote_compactM]
  rfl

/-- Exact bindings selected by the semantic mobile source; eta is not rationalized. -/
noncomputable def mobileEnvironment (alpha r p h q : ℕ) (eta : ℤ_[2]ˣ)
    (halpha : 1 ≤ alpha) (hq0 : q ≠ 0) (hqe : Even q)
    (nuP : ContinuousMonoidHom (DM alpha h : Type) Ztwo) : Environment :=
  sourceEnvironment
    (wildNuCoefficient nuP (mpcCorePresentationUnit alpha r p eta h halpha).mark)
    (eta : ℤ_[2])
    (tamePrimeToTwoCorrectionExponent hq0 hqe
      (mpcMobileNormalizedW alpha r p h eta halpha nuP)
      (tame_eval_mpcMobileNormalized_mem_inertia (q := q) eta halpha nuP))

/-- Exact arbitrary-unit, arbitrary-level, arbitrary-handle mobile source bridge. -/
theorem denote_mobileSplice (alpha r p h q : ℕ) (eta : ℤ_[2]ˣ)
    (halpha : 1 ≤ alpha) (hq0 : q ≠ 0) (hqe : Even q)
    (nuP : ContinuousMonoidHom (DM alpha h : Type) Ztwo) :
    (mobileSplice alpha r p h).denote
        (mobileEnvironment alpha r p h q eta halpha hq0 hqe nuP) =
      tameSplice (mpcMobileTameCorrectedW hq0 hqe alpha r p h eta halpha nuP)
        (Words.MCompact.mCompactW alpha h) := by
  simp only [mobileSplice, denote_splice, mobileEnvironment, denote_correct,
    denote_shear, denote_rawMobile, sourceEnvironment_eta, denote_compactM]
  rfl

#print axioms sourceEnvironment
#print axioms sourceEnvironment_k
#print axioms sourceEnvironment_eta
#print axioms shearSubst
#print axioms shear
#print axioms correct
#print axioms denote_shear
#print axioms denote_correct
#print axioms pairSplice
#print axioms mobileSplice
#print axioms pairEnvironment
#print axioms denote_pairSplice
#print axioms mobileEnvironment
#print axioms denote_mobileSplice

end GQ2.Dyadic.GeneralTemplate
