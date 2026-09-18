/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, and OpenAI Codex
-/
import GQ2.Dyadic.Word.Export
import GQ2.Dyadic.TameShadowWord

/-!
# STAGED exact symbolic exponent templates

This is an additive, separately named format, not a change to frozen S1.1.
Named parameters denote actual `Z_2`/`Zhat` values supplied by a Lean environment.
No rationality, finite precision, or computability of those values is assumed.
The syntax is finite; discrete structural parameters belong to tree factories.
-/

namespace GQ2.Dyadic.GeneralTemplate

open GQ2

/-- Exact two-adic expressions, distinguished from profinite exponents. -/
inductive PadicTerm where
  | integer (value : ℤ)
  | parameter (name : String) (index : ℕ)
  deriving Repr, DecidableEq

/-- Exact profinite expressions. `etaHat` is semantic, not a rational display. -/
inductive ProfiniteTerm where
  | integer (value : ℤ)
  | omega2
  | padicOmega (value : PadicTerm)
  | etaHat (value : PadicTerm)
  | parameter (name : String)
  deriving Repr, DecidableEq

/-- Bindings are mathematical values. JSON serializes names, never these values. -/
structure Environment where
  padic : String → ℕ → ℤ_[2]
  profinite : String → Zhat

noncomputable def PadicTerm.denote (env : Environment) : PadicTerm → ℤ_[2]
  | .integer z => z
  | .parameter name index => env.padic name index

noncomputable def ProfiniteTerm.denote (env : Environment) : ProfiniteTerm → Zhat
  | .integer z => Zhat.ofInt z
  | .omega2 => GQ2.omega2
  | .padicOmega z => padicOmega2 (z.denote env)
  | .etaHat z => etaHatZ (z.denote env)
  | .parameter name => env.profinite name

/-- The single staged expression tree. Products remain binary and retain every
trailing identity present in the semantic source; no normalization precedes hashing. -/
inductive Tree (Gen : Type*) where
  | one
  | gen (g : Gen)
  | mul (left right : Tree Gen)
  | inv (word : Tree Gen)
  | conj (word conjugator : Tree Gen)
  | comm (left right : Tree Gen)
  | zpow (word : Tree Gen) (power : ℤ)
  | z2pow (word : Tree Gen) (power : PadicTerm)
  | profPow (word : Tree Gen) (power : ProfiniteTerm)
  deriving Repr

namespace Tree

variable {Gen Gen' : Type*}

noncomputable def denote (env : Environment) : Tree Gen → PWord Gen
  | .one => .one
  | .gen g => .gen g
  | .mul u v => .mul (denote env u) (denote env v)
  | .inv u => .inv (denote env u)
  | .conj u v => .conj (denote env u) (denote env v)
  | .comm u v => .comm (denote env u) (denote env v)
  | .zpow u k => .zpow (denote env u) k
  | .z2pow u k => .z2pow (denote env u) (k.denote env)
  | .profPow u k => .profPow (denote env u) (k.denote env)

def prodList : List (Tree Gen) → Tree Gen
  | [] => .one
  | w :: ws => .mul w (prodList ws)

def subst (phi : Gen → Tree Gen') : Tree Gen → Tree Gen'
  | .one => .one
  | .gen g => phi g
  | .mul u v => .mul (subst phi u) (subst phi v)
  | .inv u => .inv (subst phi u)
  | .conj u v => .conj (subst phi u) (subst phi v)
  | .comm u v => .comm (subst phi u) (subst phi v)
  | .zpow u k => .zpow (subst phi u) k
  | .z2pow u k => .z2pow (subst phi u) k
  | .profPow u k => .profPow (subst phi u) k

@[simp] theorem denote_prodList (env : Environment) (ws : List (Tree Gen)) :
    (prodList ws).denote env = PWord.prodList (ws.map (denote env)) := by
  induction ws with
  | nil => rfl
  | cons w ws ih => exact congrArg (PWord.mul (denote env w)) ih

/-- Generator substitution is exact syntax transport, before any group evaluation. -/
@[simp] theorem denote_subst (env : Environment) (phi : Gen → Tree Gen')
    (w : Tree Gen) :
    (w.subst phi).denote env = PWord.subst (fun g => (phi g).denote env) (w.denote env) := by
  induction w <;> simp_all [subst, denote]

end Tree

/-- The proved semantic tame shadow, not frozen S1.1's unrelated `Shadow` node. -/
def shadowSubst {n : ℕ} : Generator n → Tree (Generator n)
  | .sigma => .gen .sigma
  | .tau => .one
  | .wild i => .mul (.profPow (.mul (.gen (.wild i)) (.gen .tau)) .omega2)
      (.inv (.profPow (.gen .tau) .omega2))

def shadow {n : ℕ} (w : Tree (Generator n)) : Tree (Generator n) :=
  w.subst shadowSubst

def splice {n : ℕ} (R H : Tree (Generator n)) : Tree (Generator n) :=
  .mul (.mul (shadow R) H) (.inv (shadow H))

@[simp] theorem denote_shadow {n : ℕ} (env : Environment) (w : Tree (Generator n)) :
    (shadow w).denote env = tameShadow (w.denote env) := by
  rw [shadow, Tree.denote_subst]
  unfold tameShadow
  congr 1
  funext g
  cases g <;> rfl

@[simp] theorem denote_splice {n : ℕ} (env : Environment) (R H : Tree (Generator n)) :
    (splice R H).denote env = tameSplice (R.denote env) (H.denote env) := by
  simp only [splice, Tree.denote, denote_shadow, tameSplice]

/-! The JSON serializer is a direct traversal of this same tree. -/

open Export (jsonString intToString natToString)

def PadicTerm.toJson : PadicTerm → String
  | .integer z => "{\"type\":\"integer\",\"value\":" ++ intToString z ++ "}"
  | .parameter name index => "{\"index\":" ++ natToString index ++
      ",\"name\":" ++ jsonString name ++ ",\"type\":\"parameter\"}"

def ProfiniteTerm.toJson : ProfiniteTerm → String
  | .integer z => "{\"type\":\"integer\",\"value\":" ++ intToString z ++ "}"
  | .omega2 => "{\"type\":\"omega2\"}"
  | .padicOmega z => "{\"type\":\"padic_omega\",\"value\":" ++ z.toJson ++ "}"
  | .etaHat z => "{\"type\":\"eta_hat\",\"value\":" ++ z.toJson ++ "}"
  | .parameter name => "{\"name\":" ++ jsonString name ++ ",\"type\":\"parameter\"}"

def Tree.toJson {Gen : Type*} (name : Gen → String) : Tree Gen → String
  | .one => "{\"op\":\"one\"}"
  | .gen g => "{\"name\":" ++ jsonString (name g) ++ ",\"op\":\"gen\"}"
  | .mul u v => "{\"left\":" ++ u.toJson name ++
      ",\"op\":\"mul\",\"right\":" ++ v.toJson name ++ "}"
  | .inv w => "{\"op\":\"inv\",\"word\":" ++ w.toJson name ++ "}"
  | .conj w v => "{\"by\":" ++ v.toJson name ++
      ",\"op\":\"conj\",\"word\":" ++ w.toJson name ++ "}"
  | .comm u v => "{\"left\":" ++ u.toJson name ++
      ",\"op\":\"comm\",\"right\":" ++ v.toJson name ++ "}"
  | .zpow w k => "{\"op\":\"zpow\",\"power\":" ++ intToString k ++
      ",\"word\":" ++ w.toJson name ++ "}"
  | .z2pow w k => "{\"op\":\"z2pow\",\"power\":" ++ k.toJson ++
      ",\"word\":" ++ w.toJson name ++ "}"
  | .profPow w k => "{\"op\":\"prof_pow\",\"power\":" ++ k.toJson ++
      ",\"word\":" ++ w.toJson name ++ "}"

/-- Canonical names encode the complete alphabet, independently of display aliases. -/
def generatorName {n : ℕ} : Generator n → String
  | .sigma => "sigma"
  | .tau => "tau"
  | .wild i => "x" ++ natToString i.val

#print axioms PadicTerm.denote
#print axioms ProfiniteTerm.denote
#print axioms Tree.denote
#print axioms Tree.prodList
#print axioms Tree.subst
#print axioms Tree.denote_prodList
#print axioms Tree.denote_subst
#print axioms shadowSubst
#print axioms shadow
#print axioms splice
#print axioms denote_shadow
#print axioms denote_splice
#print axioms PadicTerm.toJson
#print axioms ProfiniteTerm.toJson
#print axioms Tree.toJson
#print axioms generatorName

end GQ2.Dyadic.GeneralTemplate
