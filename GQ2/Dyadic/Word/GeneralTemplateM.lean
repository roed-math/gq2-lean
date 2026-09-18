/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, and OpenAI Codex
-/
import GQ2.Dyadic.Word.GeneralTemplate
import GQ2.Dyadic.Instances.EvenMHeadHandlePairSource
import GQ2.Dyadic.SelectedEta

/-!
# STAGED arbitrary-rank M source tree factories

These computable factories quote the exact semantic syntax, including trailing
identities and the no-handle-factor convention at rank zero. Their denotation
proofs are uniform in all discrete parameters, not per-fixture checks.
-/

namespace GQ2.Dyadic.GeneralTemplate

open GQ2.Dyadic.Words
open Instances.EvenMHeadHandleSource Instances.EvenMHeadHandlePairSource

private def sig2 {n : ℕ} : Tree (Generator n) := .profPow (.gen .sigma) .omega2

private def core (h : ℕ) (i : Fin 3) : Tree (Generator (2 + 2 * h)) :=
  .gen (coreLetter h i)

private def delta (h : ℕ) (i : Fin 3) : Tree (Generator (2 + 2 * h)) :=
  Tree.prodList [.profPow (Tree.prodList [core h i, .gen .tau]) .omega2, .inv (core h i)]

private def handles (h : ℕ) : Tree (Generator (2 + 2 * h)) :=
  Tree.prodList ((List.finRange h).map fun j => .comm (.gen (handleU j)) (.gen (handleV j)))

private def handleTail : (h : ℕ) → List (Tree (Generator (2 + 2 * h)))
  | 0 => []
  | h + 1 => [handles (h + 1)]

private theorem denote_handles (env : Environment) (h : ℕ) :
    (handles h).denote env = handlesW h := by
  simp [handles, handlesW, Tree.denote_prodList, List.map_map, Function.comp_def, Tree.denote]

private theorem denote_handleTail (env : Environment) (h : ℕ) :
    (handleTail h).map (Tree.denote env) = handleTailW h := by
  cases h <;> simp [handleTail, handleTailW, denote_handles]

private def compactA (alpha h : ℕ) : Tree (Generator (2 + 2 * h)) :=
  Tree.prodList [.inv (core h 0), .zpow sig2 (-(m alpha : ℤ))]

private def compactJ (h : ℕ) : Tree (Generator (2 + 2 * h)) :=
  Tree.prodList [.inv (.conj (core h 2) (.gen .sigma)),
    .profPow (Tree.prodList [core h 2, .gen .tau]) .omega2]

private def compactE (alpha h : ℕ) : Tree (Generator (2 + 2 * h)) :=
  Tree.prodList [.conj (delta h 1) (.zpow sig2 (2 * (m alpha : ℤ))),
    .conj (delta h 1) (.zpow sig2 (m alpha : ℤ)),
    .conj (delta h 0) (.zpow sig2 (m alpha : ℤ)), delta h 0]

/-- Exact compact-M tree at every discrete alpha and handle rank. -/
def compactM (alpha h : ℕ) : Tree (Generator (2 + 2 * h)) :=
  Tree.prodList ([.zpow (compactA alpha h) 2,
    .comm (compactA alpha h) (core h 1), .zpow sig2 (2 * (m alpha : ℤ)),
    compactJ h, compactE alpha h] ++ handleTail h)

@[simp] theorem denote_compactM (env : Environment) (alpha h : ℕ) :
    (compactM alpha h).denote env = MCompact.mCompactW alpha h := by
  simp only [compactM, Tree.denote_prodList, List.map_append, denote_handleTail]
  simp [MCompact.mCompactW, MCompact.mFactors, MCompact.a0W, MCompact.j2W,
    MCompact.eRevW, MCompact.deltaC, MCompact.mOf, m, compactA, compactJ, compactE,
    delta, sig2, core, Tree.denote_prodList, Tree.denote, ProfiniteTerm.denote,
    sigma2W, PWord.omega2Pow, PWord.prodList]

/-- Exact whole-pair promotion; the generator permutation is part of the tree. -/
def rawPair (alpha : ℕ) {h : ℕ} (j : Fin h) : Tree (Generator (2 + 2 * h)) :=
  ((compactM alpha h).subst (fun g => .gen (headHandleSwap j g))).subst
    (fun g => .gen (tailHandleSwap j g))

@[simp] theorem denote_rawPair (env : Environment) (alpha : ℕ) {h : ℕ} (j : Fin h) :
    (rawPair alpha j).denote env = headHandlePairCompactW alpha j := by
  simp only [rawPair, Tree.denote_subst, Tree.denote, denote_compactM]
  rfl

private def sig2Pow {h : ℕ} : ℕ → Tree (Generator (2 + 2 * h))
  | 1 => sig2
  | k => .zpow sig2 (k : ℤ)

private def pcC (h s : ℕ) : Tree (Generator (2 + 2 * h)) :=
  Tree.prodList [core h 2, .zpow sig2 (s : ℤ)]

private def pcA (h s m : ℕ) : Tree (Generator (2 + 2 * h)) :=
  Tree.prodList [.inv (core h 0), .zpow (pcC h s) (-(m : ℤ))]

private def pcB (h : ℕ) : ℕ → Tree (Generator (2 + 2 * h))
  | 0 => core h 1
  | p => Tree.prodList [core h 1, sig2Pow p]

private def pcE01 (h a b : ℕ) : Tree (Generator (2 + 2 * h)) :=
  Tree.prodList [.conj (Tree.prodList [.conj (delta h 1) (.zpow sig2 (b : ℤ)),
    delta h 1, delta h 0]) (.zpow sig2 (a : ℤ)), delta h 0]

private def pcZ (h : ℕ) : ℕ → Tree (Generator (2 + 2 * h))
  | 0 => .zpow (delta h 2) 2
  | p => Tree.prodList [delta h 2, .conj (delta h 2) (sig2Pow p)]

private def pcE2 (h s m p : ℕ) : Tree (Generator (2 + 2 * h)) :=
  Tree.prodList [.conj (delta h 2) (.zpow sig2 (s : ℤ)),
    .conj (Tree.prodList ((List.range m).map fun j =>
      .conj (pcZ h p) (.zpow (.zpow sig2 (s : ℤ)) (j + 1 : ℤ))))
      (.zpow sig2 ((s * m : ℕ) : ℤ))]

private def pcCHat (h s : ℕ) : Tree (Generator (2 + 2 * h)) :=
  .zpow sig2 (s : ℤ)

private def pcAHat (h s m : ℕ) : Tree (Generator (2 + 2 * h)) :=
  Tree.prodList [.inv (delta h 0), .zpow (pcCHat h s) (-(m : ℤ))]

private def pcBHat (h : ℕ) : ℕ → Tree (Generator (2 + 2 * h))
  | 0 => delta h 1
  | p => Tree.prodList [delta h 1, sig2Pow p]

/-- Semantic Mpc with an arbitrary exact two-adic eta parameter; no rational display. -/
def rawMobile (alpha r p h : ℕ) : Tree (Generator (2 + 2 * h)) :=
  let D : Tree (Generator (2 + 2 * h)) := .profPow (.gen .sigma) (.etaHat (.parameter "eta" 0))
  Tree.prodList
    ([.zpow (pcA h (s r) (m alpha)) 2,
      .comm (pcA h (s r) (m alpha)) (pcB h p),
      .zpow (pcC h (s r)) ((2 ^ alpha : ℕ) : ℤ), .comm (pcC h (s r)) D,
      pcE01 h (p + s r * m alpha) (s r * m alpha), pcE2 h (s r) (m alpha) p] ++
     [.zpow (pcAHat h (s r) (m alpha)) 2,
      .comm (pcAHat h (s r) (m alpha)) (pcBHat h p),
      .zpow (pcCHat h (s r)) ((2 ^ alpha : ℕ) : ℤ), .comm (pcCHat h (s r)) D,
      pcE01 h (p + s r * m alpha) (s r * m alpha)] ++
     [.zpow (delta h 0) 2, .comm (delta h 0) (delta h 1)] ++ handleTail h)

private theorem denote_pcBlocks (env : Environment) (h s m a b p : ℕ) :
    (pcA h s m).denote env = Mpc.aW h s m ∧
    (pcB h p).denote env = Mpc.bW h p ∧
    (pcC h s).denote env = Mpc.c0W h s ∧
    (pcE01 h a b).denote env = Mpc.e01W h a b ∧
    (pcE2 h s m p).denote env = Mpc.e2W h s m p ∧
    (pcAHat h s m).denote env = Mpc.aHatW h s m ∧
    (pcBHat h p).denote env = Mpc.bHatW h p ∧
    (pcCHat h s).denote env = Mpc.c0HatW h s := by
  have hsig (k : ℕ) : (sig2Pow (h := h) k).denote env = Mpc.sig2PowW h k := by
    match k with
    | 0 => rfl
    | 1 => rfl
    | k + 2 => rfl
  cases p <;>
    simp [pcA, pcB, pcC, pcE01, pcE2, pcZ, pcAHat, pcBHat, pcCHat,
      Mpc.aW, Mpc.bW, Mpc.c0W, Mpc.e01W, Mpc.e2W, Mpc.zW, Mpc.aHatW,
      Mpc.bHatW, Mpc.c0HatW, Mpc.dW, Mpc.uW, Export.orbitNormFactors,
      Tree.denote_prodList, List.map_map, Function.comp_def, Tree.denote, hsig, delta, core, sig2,
      ProfiniteTerm.denote, sigma2W, PWord.omega2Pow, PWord.prodList]

@[simp] theorem denote_rawMobile (env : Environment) (alpha r p h : ℕ) :
    (rawMobile alpha r p h).denote env = Mpc.mpcWAt alpha r p h
      (.profPow (.gen .sigma) (etaHatZ (env.padic "eta" 0))) := by
  rcases denote_pcBlocks env h (s r) (m alpha)
    (p + s r * m alpha) (s r * m alpha) p with ⟨hA, hB, hC, hE01, hE2, hAH, hBH, hCH⟩
  simp only [rawMobile, Tree.denote_prodList, List.map_append, List.map_cons, List.map_nil,
    Tree.denote, hA, hB, hC, hE01, hE2, hAH, hBH, hCH, denote_handleTail,
    ProfiniteTerm.denote, PadicTerm.denote]
  rfl

#print axioms compactM
#print axioms denote_compactM
#print axioms rawPair
#print axioms denote_rawPair
#print axioms rawMobile
#print axioms denote_rawMobile

end GQ2.Dyadic.GeneralTemplate
