/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, and OpenAI Codex
-/
import GQ2.Dyadic.Word.GeneralTemplateSplice

/-!
# STAGED one-tree JSON exporter

The executable emits a separately versioned, domain-separated artifact from
the exact computable tree whose denotation is proved in GeneralTemplateSplice.
It neither reads nor writes the frozen S1.1 hash manifest.
-/

namespace GQ2.Dyadic.GeneralTemplate

open Export (jsonString natToString)

def stagedSchema : String := "gq2.w361.general-template.v1.staged"

def hashDomain : String := "GQ2-W361-GENERAL-TEMPLATE\x00"

private def payload {n : ℕ} (family binding bridge structural : String)
    (w : Tree (Generator n)) : String :=
  "{\"alphabet_degree\":" ++ natToString n ++
  ",\"binding\":" ++ jsonString binding ++
  ",\"bridge\":" ++ jsonString bridge ++
  ",\"family\":" ++ jsonString family ++
  ",\"schema\":" ++ jsonString stagedSchema ++
  ",\"structural\":" ++ structural ++
  ",\"tree\":" ++ w.toJson generatorName ++ "}"

/-- Canonical staged pair payload, before its separately domain-separated hash. -/
def pairPayload (alpha h : ℕ) (j : Fin h) : String :=
  payload "pair" "GQ2.Dyadic.GeneralTemplate.pairEnvironment"
    "GQ2.Dyadic.GeneralTemplate.denote_pairSplice"
    ("{\"alpha\":" ++ natToString alpha ++ ",\"h\":" ++ natToString h ++
      ",\"j\":" ++ natToString j.val ++ "}") (pairSplice alpha j)

/-- Canonical staged mobile payload: eta and all shear coefficients remain symbolic. -/
def mobilePayload (alpha r p h : ℕ) : String :=
  payload "mobile" "GQ2.Dyadic.GeneralTemplate.mobileEnvironment"
    "GQ2.Dyadic.GeneralTemplate.denote_mobileSplice"
    ("{\"alpha\":" ++ natToString alpha ++ ",\"h\":" ++ natToString h ++
      ",\"p\":" ++ natToString p ++ ",\"r\":" ++ natToString r ++ "}")
    (mobileSplice alpha r p h)

def payloadHash (canonicalPayload : String) : String :=
  Export.Sha256.hex (hashDomain ++ canonicalPayload)

def envelope (canonicalPayload : String) : String :=
  "{\"payload\":" ++ canonicalPayload ++ ",\"status\":\"STAGED\",\"template_hash\":" ++
    jsonString (payloadHash canonicalPayload) ++ "}"

private def parseNat (name value : String) : IO Nat :=
  match value.toNat? with
  | some n => pure n
  | none => throw (IO.userError (name ++ " must be a natural number"))

/-- Emit one artifact. The prefix isolates JSON from Lean declaration-audit output. -/
def exportMain (args : List String) : IO Unit := do
  let result ← match args with
    | ["pair", a, h, j] => do
        let alpha ← parseNat "alpha" a
        let handles ← parseNat "h" h
        let selected ← parseNat "j" j
        if hj : selected < handles then
          pure (pairPayload alpha handles ⟨selected, hj⟩)
        else throw (IO.userError "pair requires j < h")
    | ["mobile", a, r, p, h] => do
        let alpha ← parseNat "alpha" a
        let level ← parseNat "r" r
        let phase ← parseNat "p" p
        let handles ← parseNat "h" h
        pure (mobilePayload alpha level phase handles)
    | _ => throw (IO.userError "usage: pair ALPHA H J | mobile ALPHA R P H")
  IO.println ("W361_GENERAL_TEMPLATE_JSON=" ++ envelope result)

#print axioms stagedSchema
#print axioms hashDomain
#print axioms pairPayload
#print axioms mobilePayload
#print axioms payloadHash
#print axioms envelope
#print axioms exportMain

end GQ2.Dyadic.GeneralTemplate

def main (args : List String) : IO Unit := GQ2.Dyadic.GeneralTemplate.exportMain args

#print axioms main
