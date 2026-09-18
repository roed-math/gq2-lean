/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, and OpenAI Codex
-/
import GQ2.Dyadic.Word.GeneralFoxTemplate
import GQ2.Dyadic.Word.Export

/-!
# STAGED JSON export of the same typed symbolic Fox profile

The direct serializer traverses input rows, operation lists (including inverses),
and target rows from one Profile value. q and k remain symbolic; only the alphabet
handle count is supplied to the executable. The hash identifies this symbolic
template, not a coefficient module, an instantiated action period, a source word,
or a proof. Actual record bindings are checked in TameSpliceFoxTemplateBinding.
This executable is separate from the frozen word exporter and its manifests.
-/

namespace GQ2.Dyadic.GeneralFoxTemplate
open Export (jsonString intToString natToString)

def generatorJson {n : ℕ} : Generator n → String
  | .sigma => "{\"kind\":\"sigma\"}"
  | .tau => "{\"kind\":\"tau\"}"
  | .wild i => "{\"index\":" ++ natToString i.val ++ ",\"kind\":\"wild\"}"

def symbolJson {n : ℕ} : TameSym n → String
  | .gen g z => "{\"generator\":" ++ generatorJson g ++
      ",\"kind\":\"generator_power\",\"power\":" ++ intToString z ++ "}"
  | .sigma2 z => "{\"kind\":\"sigma2_power\",\"power\":" ++ intToString z ++ "}"
  | .proj => "{\"kind\":\"projector\"}"

def Coeff.toJson {n : ℕ} : Coeff n → String
  | .zero => "{\"op\":\"zero\"}"
  | .one => "{\"op\":\"one\"}"
  | .atom s => "{\"op\":\"atom\",\"symbol\":" ++ symbolJson s ++ "}"
  | .add a b => "{\"left\":" ++ a.toJson ++ ",\"op\":\"add\",\"right\":" ++ b.toJson ++ "}"
  | .neg a => "{\"op\":\"neg\",\"value\":" ++ a.toJson ++ "}"
  | .comp a b => "{\"inner\":" ++ b.toJson ++ ",\"op\":\"comp\",\"outer\":" ++ a.toJson ++ "}"
  | .oddSum g sign => "{\"generator\":" ++ generatorJson g ++
      ",\"op\":\"odd_power_sum\",\"parameter\":\"k\",\"sign\":" ++ intToString sign ++ "}"
  | .normSum g => "{\"generator\":" ++ generatorJson g ++
      ",\"op\":\"norm_power_sum\",\"parameter\":\"q\"}"

def RowOp.toJson {n : ℕ} : RowOp n → String
  | .swap => "{\"op\":\"swap\"}"
  | .addFst c => "{\"coefficient\":" ++ c.toJson ++ ",\"op\":\"add_fst\"}"
  | .addSnd c => "{\"coefficient\":" ++ c.toJson ++ ",\"op\":\"add_snd\"}"
  | .scaleFst c d => "{\"forward\":" ++ c.toJson ++
      ",\"inverse\":" ++ d.toJson ++ ",\"op\":\"scale_fst\"}"
  | .scaleSnd c d => "{\"forward\":" ++ c.toJson ++
      ",\"inverse\":" ++ d.toJson ++ ",\"op\":\"scale_snd\"}"

def ColOp.toJson {n : ℕ} : ColOp n → String
  | .swap g h => "{\"left\":" ++ generatorJson g ++
      ",\"op\":\"swap\",\"right\":" ++ generatorJson h ++ "}"
  | .transvect g h c => "{\"coefficient\":" ++ c.toJson ++
      ",\"op\":\"transvect\",\"source\":" ++ generatorJson h ++
      ",\"target\":" ++ generatorJson g ++ "}"
  | .scale g c d => "{\"forward\":" ++ c.toJson ++
      ",\"generator\":" ++ generatorJson g ++ ",\"inverse\":" ++ d.toJson ++ ",\"op\":\"scale\"}"

def PivotRow.toJson {n : ℕ} : PivotRow n → String
  | .zero => "{\"op\":\"zero_row\"}"
  | .single g => "{\"generator\":" ++ generatorJson g ++ ",\"op\":\"identity_pivot\"}"

def LinearRow.toJson {n : ℕ} : LinearRow n → String
  | .zero => "{\"op\":\"zero_row\"}"
  | .term c g => "{\"coefficient\":" ++ c.toJson ++
      ",\"generator\":" ++ generatorJson g ++ ",\"op\":\"term\"}"
  | .add a b => "{\"left\":" ++ a.toJson ++ ",\"op\":\"add\",\"right\":" ++ b.toJson ++ "}"

def Profile.toJson {n : ℕ} (p : Profile n) : String :=
  "{\"column_ops\":[" ++ String.intercalate "," (p.colOps.map ColOp.toJson) ++
  "],\"input_rows\":[" ++ p.inputFirst.toJson ++ "," ++ p.inputSecond.toJson ++
  "],\"row_ops\":[" ++ String.intercalate "," (p.rowOps.map RowOp.toJson) ++
  "],\"target_rows\":[" ++ p.first.toJson ++ "," ++ p.second.toJson ++ "]}"

def foxTemplateSchema : String := "gq2.w361.fox-template.v1.staged"
def foxTemplateHashDomain : String := "GQ2-W361-FOX-TEMPLATE\x00"

private def sectorJson {n : ℕ} (name interpretation period : String) (p : Profile n) : String :=
  "{\"certificate_bridges\":{\"mobile\":" ++
    jsonString ("GQ2.Dyadic.GeneralFoxTemplate." ++ name ++ "_mobile_signature") ++
    ",\"pair\":" ++ jsonString ("GQ2.Dyadic.GeneralFoxTemplate." ++ name ++ "_pair_signature") ++
  "},\"denotation_bridge\":" ++ jsonString ("GQ2.Dyadic.GeneralFoxTemplate.denote_" ++ name) ++
  ",\"input_evaluation_bridge\":" ++ jsonString ("GQ2.Dyadic.GeneralFoxTemplate." ++ name ++ "_input_apply") ++
  ",\"interpretation\":" ++ jsonString interpretation ++
  ",\"k_binding\":" ++ jsonString period ++ ",\"sector\":" ++ jsonString name ++
  ",\"tree\":" ++ p.toJson ++ "}"

/-- q and k stay symbolic. Only the alphabet's structural handle count is instantiated. -/
def foxTemplatePayload (h : ℕ) : String :=
  "{\"alphabet\":{\"h\":" ++ natToString h ++ ",\"n\":" ++ natToString (2+2*h) ++
  ",\"wild_count\":" ++ natToString (2+2*h+1) ++ ",\"x2\":2}," ++
  "\"application_scope\":\"Actual pair/mobile splice certificates under their stated hypotheses; pair also requires a selected handle.\"," ++
  "\"composition\":\"comp(outer,inner) applies inner first; row list applies head first; column list denotes head composed with tail.\"," ++
  "\"hash_scope\":\"Symbolic template identity only; no q, k, finite coefficient space, marking, or source exponent values are selected.\"," ++
  "\"parameters\":{\"k\":{\"domain\":\"Nat\",\"role\":\"Coefficient-action-dependent half-period: actual odd action order equals 2*k+1. Not handle rank.\"}," ++
  "\"q\":{\"domain\":\"Nat\",\"role\":\"Source residue size, nonzero and even in certified uses; norm sum has q terms.\"}}," ++
  "\"profiles\":[" ++ sectorJson "scalar" "TameSym.splitEnd" "unused (certificate bridge chooses 0)" (scalar (2+2*h)) ++
  "," ++ sectorJson "unramified" "TameSym.splitEnd"
    "sigmaActionHalfPeriod(t,A) = orderOf(actual sigma action)/2"
    (unramified (Certificates.x2Idx h)) ++
  "," ++ sectorJson "ramified" "TameSym.ramifiedEnd"
    "tauActionHalfPeriod(t,A) = orderOf(actual tau action)/2"
    (ramified (Certificates.x2Idx h)) ++
  "],\"schema\":" ++ jsonString foxTemplateSchema ++ "}"

def foxTemplateEnvelope (h : ℕ) : String :=
  let payload := foxTemplatePayload h
  "{\"payload\":" ++ payload ++ ",\"status\":\"STAGED\",\"template_hash\":" ++
    jsonString (Export.Sha256.hex (foxTemplateHashDomain ++ payload)) ++ "}"

def foxTemplateExportMain (args : List String) : IO Unit := do
  let h ← match args with
    | ["all", h] => match h.toNat? with
      | some h => pure h
      | none => throw (IO.userError "h must be a natural number")
    | _ => throw (IO.userError "usage: all H (q and k remain symbolic)")
  IO.println ("W361_FOX_TEMPLATE_JSON=" ++ foxTemplateEnvelope h)

#print axioms generatorJson
#print axioms symbolJson
#print axioms Coeff.toJson
#print axioms RowOp.toJson
#print axioms ColOp.toJson
#print axioms PivotRow.toJson
#print axioms LinearRow.toJson
#print axioms Profile.toJson
#print axioms foxTemplateSchema
#print axioms foxTemplateHashDomain
#print axioms foxTemplatePayload
#print axioms foxTemplateEnvelope
#print axioms foxTemplateExportMain

end GQ2.Dyadic.GeneralFoxTemplate

def main (args : List String) : IO Unit := GQ2.Dyadic.GeneralFoxTemplate.foxTemplateExportMain args
#print axioms main
