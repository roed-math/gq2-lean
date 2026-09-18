/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, and OpenAI Codex
-/
import GQ2.Dyadic.Word.GeneralPhaseTemplate

/-! Separate executable for the STAGED typed quadratic-phase tree and certified matrices. -/

namespace GQ2.Dyadic.GeneralPhaseTemplate

/-- Export one rank, with a prefix separating JSON from declaration-audit output. -/
def exportMain (args : List String) : IO Unit := do
  let h ← match args with
    | [value] => match value.toNat? with
      | some h => pure h
      | none => throw (IO.userError "h must be a natural number")
    | _ => throw (IO.userError "usage: H")
  IO.println ("W361_PHASE_TEMPLATE_JSON=" ++ envelope (compactPayload h))

#print axioms exportMain
end GQ2.Dyadic.GeneralPhaseTemplate

def main (args : List String) : IO Unit := GQ2.Dyadic.GeneralPhaseTemplate.exportMain args
#print axioms main
