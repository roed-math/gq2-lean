/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu
-/
import GQ2.Dyadic.Instances.GammaLReconstruction
import GQ2.Dyadic.Instances.WordPhaseCompactNFinal
import GQ2.Dyadic.Instances.NpcCandidateRN
import GQ2.Dyadic.Word.Export

/-!
# STAGED serializer for the L/N0/Npc Stokes chain (ledger item 6)

This is an exporter driver, not a library module: it carries a global `main` and stays
outside `GQ2.lean`, like `scripts/w362_ln_fox_export.lean` and
`scripts/w363_ln_input_export.lean`.

**What this exporter can and cannot be.** Items 3, 4 and 5 are *data*: `FoxCoeff` trees and
operation lists, which an exporter serializes. Item 6 is not. `StokesDualityCertificate` is a
`Prop`, a four-fold conjunction of universally quantified counting and separation statements
over types that do not exist until a recursion frame is supplied. There is no matrix, no
chain complex object and no coefficient tree to serialize, and this driver does not invent
one. What it does serialize is the part of item 6 that genuinely is data:

* the **wiring**: which declaration proves the chain for the family, which record consumes it,
  and in which field;
* the **clause structure**: the four conjuncts in their actual order, each with its role;
* the **numeric multipliers the counting clauses assert**, which are literal exponents of the
  `standardNumerics` record, bound by `rfl`.

**What the field bindings do and do not establish.** `StokesDualityCertificate` is a `Prop`,
and Lean has definitional proof irrelevance, so `record.stokes = producer` is `rfl` for *any*
producer whose type is the field's type. The bindings below therefore certify a **statement
identity**: the producer proves exactly the statement the record's `stokes` field demands, at
the record's own parameters. They do **not** certify that the record was built from that
proof term, and nothing here should be read as saying so. The JSON labels the bridge kind
`field_statement_identity` for that reason, not `record_target`, which is what the item 3 and
item 4/5 exporters use for a genuine data field.

**The Npc degree.** The Npc producer is stated at degree `2*h+2` and the record's field at
`2+2*h`. Those are not definitionally equal at a variable `h`, and the record's own field is
filled by rewriting along the equality. So the Npc binding is a degree normalization, not the
`rfl` the L and N0 bindings are, and the JSON says so with its own bridge kind and names the
normalization theorem.

Scope. No coefficient module, marking, field, resolver, `eta` or source certificate is
selected, and this is not an approved appendix, manifest entry, gate or release.
-/

namespace GQ2.Dyadic.W363LNStokes

open GQ2 GQ2.Dyadic.Words
open GQ2.Dyadic.Export (jsonString natToString)

/-! ## Signature theorems, part 1: the numeric multipliers the clauses assert

`standardNumerics` is the only place in the development where a degree-`n` numeric formula is
written down, so the counting clauses' multipliers are literal exponents there. Both are
`rfl`. -/

/-- The T-cocycle clause's multiplier at standard numerics: `|T| ^ (n+1)`. -/
theorem standardNumerics_tMult (n T : ℕ) : (standardNumerics n).tMult T = T ^ (n + 1) := rfl

/-- The V-cocycle clause's inner multiplier at standard numerics: `|V| ^ n`. The outer `|V|`
in that clause is `#B¹` and is degree-independent, so it carries no exponent. -/
theorem standardNumerics_h1Mult (n V : ℕ) : (standardNumerics n).h1Mult V = V ^ n := rfl

/-! ## Signature theorems, part 2: the producer proves the record's own field

Statement identity, not proof identity: see the module docstring. -/

/-- The L chain: the action-image producer's statement IS the `stokes` field of the L word
certificate record, at the record's own parameters. -/
theorem lStokes_field {h q : ℕ} (hq2 : 2 ≤ q) (hqe : Even q)
    (A : LSquare.LSquareAnalyticLeavesRN h q hq2 hqe) :
    (LSquare.wordCertificateRN_lSq_of_actionImage hq2 hqe A).stokes
      = LSquare.stokesDualityCertificate_of_actionImage hqe := rfl

/-- The N0 chain: same, for the compact-`N` record. -/
theorem n0Stokes_field (alpha h q : ℕ) (halpha : 2 ≤ alpha) (hq0 : q ≠ 0) (hqe : Even q) :
    (Instances.WordPhaseCompactNFinal.wPcNWordCertificateRN alpha h q halpha hq0 hqe).stokes
      = Instances.WordPhase.wPh_nCand_stokes halpha hq0 hqe := rfl

/-- The Npc degree normalization. The producer is stated at `2*h+2`, the record's field at
`2+2*h`; these are not definitionally equal at a variable `h`. -/
theorem npcStokes_degreeNormalization (h : ℕ) : 2 * h + 2 = 2 + 2 * h := by omega

/-- The two Npc chain statements are the SAME `Prop` once the degree is normalized: the
producer's statement at `2*h+2` is the record field's statement at `2+2*h`. This is the Npc
analogue of the two `rfl` bindings above, and it is what the record's own `stokes` field
tactic block does. -/
theorem npcStokes_typeNormalization (G : ProfiniteGrp) (h q : ℕ) (P : ProfiniteGrp)
    (nuP : ContinuousMonoidHom P Ztwo) (smul : DistribMulAction G (ZMod 2)) :
    StokesDualityCertificate G (2 * h + 2) q P nuP (standardNumerics (2 * h + 2)) smul
      = StokesDualityCertificate G (2 + 2 * h) q P nuP (standardNumerics (2 + 2 * h)) smul := by
  rw [npcStokes_degreeNormalization h]

/-! ## Canonical JSON serialization

Keys are emitted in ASCII order so that the bytes agree with Python's
`json.dumps(..., sort_keys=True, separators=(",",":"))` used by the checker. -/

def schema : String := "gq2.w363.ln-stokes-chain.v1.staged"
def hashDomain : String := "GQ2-W363-LN-STOKES-CHAIN\x00"
def bridgeRoot : String := "GQ2.Dyadic.W363LNStokes."
def clauseRoot : String := "GQ2.Dyadic.StokesDualityCertificate"
def numericsRoot : String := "GQ2.Dyadic.standardNumerics"

def scopeNote : String :=
  "Ledger item 6 only: the wiring, the clause structure and the numeric multipliers of the L/N0/Npc Stokes chain. No coefficient module, marking, field, resolver, eta or source certificate is selected."

def warningNote : String :=
  "StokesDualityCertificate is a Prop, so this display is NOT a rendering of the chain identity's proof and no formula is substituted for one. Lean has definitional proof irrelevance, so a field binding certifies that the producer proves exactly the statement the record's stokes field demands, at the record's own parameters, and NOT that the record was built from that proof term. The clause statements themselves remain in the packet's stored proofs transcript."

def hashScopeNote : String :=
  "Identity of the serialized wiring, clause structure and multiplier exponents at the stated discrete parameters. It is not a hash of any proof."

def statementKind : String := "field_statement_identity"
def normalizedKind : String := "degree_normalized_field"

/-- One numeric multiplier: the symbol it is applied to, the `rfl` bridge, and the literal
exponent at this instance. -/
def multiplierJson (argument bridge : String) (exponent : ℕ) : String :=
  "{\"argument\":" ++ jsonString argument ++ ",\"bridge\":" ++ jsonString bridge ++
    ",\"exponent\":" ++ natToString exponent ++ "}"

/-- One clause of the chain: its position in the conjunction, what it asserts, and, when it is
a counting clause, which multiplier carries the degree. -/
def clauseJson (position : ℕ) (id role : String) (count : String) : String :=
  "{\"count\":" ++ count ++ ",\"id\":" ++ jsonString id ++ ",\"position\":" ++
    natToString position ++ ",\"role\":" ++ jsonString role ++ "}"

def countJson (multiplier shape : String) : String :=
  "{\"multiplier\":" ++ jsonString multiplier ++ ",\"shape\":" ++ jsonString shape ++ "}"

def chain : List String :=
  [ clauseJson 1 "tcocycle_count"
      "The number of T-cocycles of the radical data equals the tMult multiplier of the T-order times the number of fixed points of the elementary dual."
      (countJson "t_mult" "card(TCocycle) = tMult(card T) * card(fixedPts(ElemDual))")
  , clauseJson 2 "separation"
      "A V-cocycle on which every T-character pairing vanishes is T-liftable: the separation half of the duality."
      "null"
  , clauseJson 3 "nondegeneracy"
      "Every nonzero T-character is nondegenerate against the obstruction pairing: some V-cocycle moves it off its value at zero."
      "null"
  , clauseJson 4 "vcocycle_count"
      "On a simple nontrivial module the number of V-cocycles equals the module order times the h1Mult multiplier of the module order."
      (countJson "h1_mult" "card(VCocycle) = card(V) * h1Mult(card V)") ]

def numericsJson (n : ℕ) : String :=
  "{\"h1_mult\":" ++ multiplierJson "card V" (bridgeRoot ++ "standardNumerics_h1Mult") n ++
  ",\"record\":" ++ jsonString numericsRoot ++
  ",\"t_mult\":" ++ multiplierJson "card T" (bridgeRoot ++ "standardNumerics_tMult") (n+1) ++
  "}"

def consumerJson (binding kind field normalization record : String) (degree : ℕ) : String :=
  "{\"binding\":" ++ jsonString binding ++ ",\"binding_kind\":" ++ jsonString kind ++
  ",\"field\":" ++ jsonString field ++ ",\"normalization\":" ++ normalization ++
  ",\"record\":" ++ jsonString record ++ ",\"record_degree\":" ++ natToString degree ++ "}"

def producerJson (declaration : String) (degree : ℕ) : String :=
  "{\"declaration\":" ++ jsonString declaration ++ ",\"degree\":" ++ natToString degree ++ "}"

def payload (family : String) (n : ℕ) (structural producer consumer : String) : String :=
  "{\"application_scope\":" ++ jsonString scopeNote ++ "," ++
  "\"chain\":[" ++ String.intercalate "," chain ++ "]," ++
  "\"clause_record\":" ++ jsonString clauseRoot ++ "," ++
  "\"consumer\":" ++ consumer ++ "," ++
  "\"family\":" ++ jsonString family ++ "," ++
  "\"hash_scope\":" ++ jsonString hashScopeNote ++ "," ++
  "\"numerics\":" ++ numericsJson n ++ "," ++
  "\"producer\":" ++ producer ++ "," ++
  "\"schema\":" ++ jsonString schema ++ "," ++
  "\"structural\":" ++ structural ++ "," ++
  "\"warning\":" ++ jsonString warningNote ++ "}"

def envelope (p : String) : String :=
  "{\"payload\":" ++ p ++ ",\"status\":\"STAGED\",\"template_hash\":" ++
    jsonString (Export.Sha256.hex (hashDomain ++ p)) ++ "}"

def structuralLN (h q : ℕ) : String :=
  "{\"h\":" ++ natToString h ++ ",\"q\":" ++ natToString q ++ "}"

def structuralNpc (h q r : ℕ) : String :=
  "{\"h\":" ++ natToString h ++ ",\"q\":" ++ natToString q ++ ",\"r\":" ++ natToString r ++ "}"

def lPayload (h q : ℕ) : String :=
  payload "L" (2*h+1) (structuralLN h q)
    (producerJson "GQ2.Dyadic.LSquare.stokesDualityCertificate_of_actionImage" (2*h+1))
    (consumerJson (bridgeRoot ++ "lStokes_field") statementKind "stokes" "null"
      "GQ2.Dyadic.LSquare.wordCertificateRN_lSq_of_actionImage" (2*h+1))

def n0Payload (h q : ℕ) : String :=
  payload "N0" (2+2*h) (structuralLN h q)
    (producerJson "GQ2.Dyadic.Instances.WordPhase.wPh_nCand_stokes" (2+2*h))
    (consumerJson (bridgeRoot ++ "n0Stokes_field") statementKind "stokes" "null"
      "GQ2.Dyadic.Instances.WordPhaseCompactNFinal.wPcNWordCertificateRN" (2+2*h))

def npcPayload (h q r : ℕ) : String :=
  payload "Npc" (2+2*h) (structuralNpc h q r)
    (producerJson "GQ2.Dyadic.Instances.NpcCandidateStokes.npcCand_stokes" (2*h+2))
    (consumerJson (bridgeRoot ++ "npcStokes_typeNormalization") normalizedKind "stokes"
      (jsonString (bridgeRoot ++ "npcStokes_degreeNormalization"))
      "GQ2.Dyadic.Instances.NpcCandidateRN.npcWordCertificateRN_of_determinant" (2+2*h))

def exportMain (args : List String) : IO Unit := do
  let p ← match args with
    | ["L", hs, qs] => match hs.toNat?, qs.toNat? with
      | some h, some q => pure (lPayload h q)
      | _, _ => throw (IO.userError "L H Q: H and Q must be natural numbers")
    | ["N0", hs, qs] => match hs.toNat?, qs.toNat? with
      | some h, some q => pure (n0Payload h q)
      | _, _ => throw (IO.userError "N0 H Q: H and Q must be natural numbers")
    | ["Npc", hs, qs, rs] => match hs.toNat?, qs.toNat?, rs.toNat? with
      | some h, some q, some r => pure (npcPayload h q r)
      | _, _, _ => throw (IO.userError "Npc H Q R: H, Q and R must be natural numbers")
    | _ => throw (IO.userError "usage: L H Q | N0 H Q | Npc H Q R")
  IO.println ("W363_LN_STOKES_JSON=" ++ envelope p)

#print axioms standardNumerics_tMult
#print axioms standardNumerics_h1Mult
#print axioms lStokes_field
#print axioms n0Stokes_field
#print axioms npcStokes_degreeNormalization
#print axioms npcStokes_typeNormalization
#print axioms exportMain

end GQ2.Dyadic.W363LNStokes

def main (args : List String) : IO Unit := GQ2.Dyadic.W363LNStokes.exportMain args
