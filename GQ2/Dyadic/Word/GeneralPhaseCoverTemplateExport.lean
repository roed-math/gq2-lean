/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, and OpenAI Codex
-/
import GQ2.Dyadic.Word.GeneralPhaseCoverTemplate

/-! Separate executable for STAGED typed compact phase-cover fields. -/

namespace GQ2.Dyadic.GeneralPhaseCoverTemplate

def exportMain (args : List String) : IO Unit := do
  let h ← match args with
    | [value] => match value.toNat? with
      | some h => pure h
      | none => throw (IO.userError "h must be a natural number")
    | _ => throw (IO.userError "usage: H")
  IO.println ("W361_PHASE_COVER_TEMPLATE_JSON=" ++ envelope (compactPayload h))

#print axioms exportMain
end GQ2.Dyadic.GeneralPhaseCoverTemplate

def main (args : List String) : IO Unit := GQ2.Dyadic.GeneralPhaseCoverTemplate.exportMain args
#print axioms main
