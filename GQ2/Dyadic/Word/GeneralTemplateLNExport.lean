/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, and OpenAI Codex
-/
import GQ2.Dyadic.Word.GeneralTemplateLNCanonical

/-!
# STAGED rank-uniform export of the unchanged legacy L/N word factories

The word grammar, constructor factories, canonical JSON and word hash are the
existing S1.1 definitions. Only a separately versioned envelope is added. It
binds the actual requested integer parameters and the uniform denotation
bridge. Exporting syntax is not supplying the additional certificate premises.
-/

namespace GQ2.Dyadic.GeneralTemplateLNExport
open GQ2 GQ2.Dyadic Words Export

def stagedSchema : String := "gq2.w361.ln-word.v1.staged"
def hashDomain : String := "GQ2-W361-LN-WORD\x00"

private def payload (degree : ℕ) (family factory binding bridge target unitBridge structural : String)
    (w : RawWord) : String :=
  "{\"alphabet_degree\":" ++ natToString degree ++
    ",\"ast_schema_version\":1,\"binding\":" ++ jsonString binding ++
    ",\"bridge\":" ++ jsonString bridge ++ ",\"factory\":" ++ jsonString factory ++
    ",\"family\":" ++ jsonString family ++ ",\"schema\":" ++ jsonString stagedSchema ++
    ",\"semantic_target\":" ++ jsonString target ++ ",\"structural\":" ++ structural ++
    ",\"tree\":" ++ canonicalJson w ++ ",\"unit_bridge\":" ++ unitBridge ++
    ",\"word_hash\":" ++ jsonString (astHash w) ++ "}"

def lPayload (h : ℕ) : String :=
  payload (2*h+1) "L" "GQ2.Dyadic.Words.LSq.rawLsq" "GQ2.Dyadic.Words.LSq.denoteCtx"
    "GQ2.Dyadic.GeneralTemplateLN.denote_canon_rawLsq" "GQ2.Dyadic.Words.LSq.lSqW" "null"
    ("{\"h\":" ++ natToString h ++ "}") (LSq.rawLsq h)

def n0Payload (alpha h : ℕ) : String :=
  payload (2+2*h) "N0" "GQ2.Dyadic.Words.rawNCompact" "GQ2.Dyadic.Words.denoteCtx"
    "GQ2.Dyadic.GeneralTemplateLN.denote_canon_rawNCompact" "GQ2.Dyadic.Words.nCompactW" "null"
    ("{\"alpha\":" ++ natToString alpha ++ ",\"h\":" ++ natToString h ++ "}")
    (Words.rawNCompact alpha h)

def npcPayload (alpha r h : ℕ) (num den : ℤ) : String :=
  payload (2+2*h) "Npc" "GQ2.Dyadic.Words.Npc.rawNpc" "GQ2.Dyadic.Words.denoteCtx"
    "GQ2.Dyadic.GeneralTemplateLN.denote_canon_rawNpc" "GQ2.Dyadic.Words.Npc.npcW"
    (jsonString "GQ2.Dyadic.GeneralTemplateLN.denote_canon_rawNpc_display")
    ("{\"alpha\":" ++ natToString alpha ++ ",\"den\":" ++ intToString den ++
      ",\"h\":" ++ natToString h ++ ",\"num\":" ++ intToString num ++
      ",\"r\":" ++ natToString r ++ "}")
    (Npc.rawNpc alpha r h num den)

def payloadHash (canonicalPayload : String) : String :=
  Sha256.hex (hashDomain ++ canonicalPayload)

def envelope (canonicalPayload : String) : String :=
  "{\"payload\":" ++ canonicalPayload ++ ",\"status\":\"STAGED\",\"template_hash\":" ++
    jsonString (payloadHash canonicalPayload) ++ "}"

private def parseNat (name value : String) : IO ℕ :=
  match value.toNat? with
  | some n => pure n
  | none => throw (IO.userError (name ++ " must be a natural number"))

private def parseOdd (name value : String) : IO ℤ := do
  match value.toInt? with
  | some n =>
      if n % 2 != 0 then pure n
      else throw (IO.userError (name ++ " must be odd"))
  | none => throw (IO.userError (name ++ " must be an integer"))

def exportMain (args : List String) : IO Unit := do
  let result ← match args with
    | ["L", h] => do
        pure (lPayload (← parseNat "h" h))
    | ["N0", a, h] => do
        pure (n0Payload (← parseNat "alpha" a) (← parseNat "h" h))
    | ["Npc", a, r, h, num, den] => do
        pure (npcPayload (← parseNat "alpha" a) (← parseNat "r" r)
          (← parseNat "h" h) (← parseOdd "num" num) (← parseOdd "den" den))
    | _ => throw (IO.userError "usage: L H | N0 ALPHA H | Npc ALPHA R H ODD_NUM ODD_DEN")
  IO.println ("W361_LN_WORD_JSON=" ++ envelope result)

#print axioms stagedSchema
#print axioms hashDomain
#print axioms lPayload
#print axioms n0Payload
#print axioms npcPayload
#print axioms payloadHash
#print axioms envelope
#print axioms exportMain
end GQ2.Dyadic.GeneralTemplateLNExport

def main (args : List String) : IO Unit := GQ2.Dyadic.GeneralTemplateLNExport.exportMain args
#print axioms main
