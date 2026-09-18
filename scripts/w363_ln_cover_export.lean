/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu
-/
import GQ2.Dyadic.Instances.GammaLSourceArfGeneral
import GQ2.Dyadic.Instances.WordPhaseCompactNFinal
import GQ2.Dyadic.Instances.NpcDeterminantFinal
import GQ2.Dyadic.Word.Export

/-!
# STAGED serializer for the L/N0/Npc affine phase-cover certificate (ledger item 9)

This is an exporter driver, not a library module: it carries a global `main` and stays
outside `GQ2.lean`, like the other W361/W362/W363 export executables.

**Item 9 is item 6's shape, with the multipliers the item-6 artifact left out.**
`AffineDeterminantCertificate` is, like `StokesDualityCertificate`, a `Prop` defined by a
conjunction of universally quantified clauses, consumed as the `determinant` field of the
same word certificate records. It has **two** clauses, not four: a Gauss-`Z` residue at a
head where the tame frame element acts trivially, using `SN.gaussUnram m`, and one where it
does not, using `SN.gaussRam m`. `scripts/w363_ln_stokes_export.lean` deliberately exports
only `tMult` and `h1Mult`, which are the multipliers its own clauses use; `gaussUnram` and
`gaussRam` belong here.

Those two multipliers carry a **sign** as well as an exponent, which the item-6 multipliers
do not: `gaussUnram m = (-1)^n * 2^(n*m)` and `gaussRam m = 2^(n*m)`. Both are `rfl`. The
sign is therefore a function of the degree parity alone, and the exported value is computed
from the formula rather than asserted: it is `-1` for L, whose degree `2h+1` is odd, and
`+1` for N0 and Npc, whose degree `2+2h` is even.

**What a field binding certifies.** `AffineDeterminantCertificate` is a `Prop` and Lean has
definitional proof irrelevance, so `record.determinant = producer` is `rfl` for any producer
whose type is the field's type. As in item 6 this is a **statement identity**, not proof
identity, and the bridge kind is `field_statement_identity`.

**Where the proof comes from differs by family, and that is separate from the bridge kind.**
At N0 and Npc the `determinant` field is filled by a theorem of the tree. At L it is filled
from a **field of an analytic-leaves record supplied as a parameter**, and the theorem that
produces that field, `determinantResidue_lSq_pow`, is available only at `q = 2^f` with `f`
odd. The artifact records that as a separate `supply` field so the two are not conflated.
Unlike item 6, **no degree normalization is needed at Npc here**: producer and record field
are both at `2+2h`.

Scope. No coefficient module, marking, field, resolver, `eta` or source certificate is
selected. This is not an approved appendix, manifest entry, gate or release.
-/

namespace GQ2.Dyadic.W363LNCover

open GQ2 GQ2.Dyadic.Words
open GQ2.Dyadic.Export (jsonString natToString intToString)

/-! ## Signature theorems, part 1: the Gauss multipliers

`standardNumerics` is the only place in the development where a degree-`n` numeric formula
is written down. Both are `rfl`. -/

/-- The unramified Gauss residue at standard numerics: `(-1)^n * 2^(n*m)`. The sign is a
function of the degree parity alone. -/
theorem standardNumerics_gaussUnram (n m : ℕ) :
    (standardNumerics n).gaussUnram m = (-1) ^ n * 2 ^ (n * m) := rfl

/-- The ramified Gauss residue at standard numerics: `2^(n*m)`, with no sign. -/
theorem standardNumerics_gaussRam (n m : ℕ) :
    (standardNumerics n).gaussRam m = 2 ^ (n * m) := rfl

/-! ## Signature theorems, part 2: the producer proves the record's own `determinant` field

Statement identity, not proof identity: see the module docstring. -/

/-- **L.** The word certificate's `determinant` field is the `determinant` field of the
analytic-leaves record it is given, not a theorem proved inside it. -/
theorem lDeterminant_field {h q : ℕ} (hq2 : 2 ≤ q) (hqe : Even q)
    (A : LSquare.LSquareAnalyticLeavesRN h q hq2 hqe) :
    (LSquare.wordCertificateRN_lSq_of_actionImage hq2 hqe A).determinant = A.determinant :=
  rfl

/-- **L, the supply.** At `q = 2^f` with `f` odd the analytic-leaves record's own field is
the determinant-residue theorem. This is where the L determinant actually comes from, and
it is the only place in the three families where the scope is a power of two with an odd
exponent rather than a condition on `alpha` and `q`. -/
theorem lDeterminant_leaves {h q : ℕ} (hq2 : 2 ≤ q) (hqe : Even q)
    {f : ℕ} (hfodd : Odd f) (hqf : q = 2 ^ f) :
    (LSquare.lSquareAnalyticLeavesRN_pow (h := h) hq2 hqe hfodd hqf).determinant
      = LSquare.determinantResidue_lSq_pow (Instances.LSquareCore.lNu h)
          (TameSpec.tameOfSpec (2 * h + 1) q (Words.LSq.lSqW h)
            (LSquare.lCanonicalTameSpecialization h q hq2 hqe))
          (LSquare.lCanonicalPro2 h q hq2 hqe) (LSquare.lCanonicalCompat h q hq2 hqe)
          (LSquare.tameOfSpec_lSq_sigma hq2 hqe) (LSquare.tameOfSpec_lSq_tau hq2 hqe)
          (LSquare.tameOfSpec_lSq_wild hq2 hqe) hfodd hqf := rfl

/-- **N0.** The compact-`N` record's `determinant` field is the tree's own theorem. -/
theorem n0Determinant_field (alpha h q : ℕ) (halpha : 2 ≤ alpha) (hq0 : q ≠ 0)
    (hqe : Even q) :
    (Instances.WordPhaseCompactNFinal.wPcNWordCertificateRN alpha h q halpha hq0
        hqe).determinant
      = Instances.WordPhaseCompactNFinal.wPcN_affineDeterminantCertificate halpha hq0 hqe :=
  rfl

/-- **Npc.** The procyclic record's `determinant` field is the tree's own theorem, at the
same degree spelling `2+2h` on both sides: item 6's degree normalization is not needed here. -/
theorem npcDeterminant_field (alpha r h q : ℕ) {eta : ℤ_[2]ˣ} (d : NpcDisplayFor eta)
    (halpha : 2 ≤ alpha) (hq0 : q ≠ 0) (hqe : Even q) :
    (Instances.NpcDeterminantFinal.npcWordCertificateRN alpha r h q d halpha hq0
        hqe).determinant
      = Instances.NpcDeterminantFinal.npcAffineDeterminantCertificate alpha r h q d halpha
          hq0 hqe := rfl

/-! ## Canonical JSON serialization

Keys are emitted in ASCII order so that the bytes agree with Python's
`json.dumps(..., sort_keys=True, separators=(",",":"))` used by the checker. -/

def schema : String := "gq2.w363.ln-phase-cover.v1.staged"
def hashDomain : String := "GQ2-W363-LN-PHASE-COVER\x00"
def bridgeRoot : String := "GQ2.Dyadic.W363LNCover."
def clauseRoot : String := "GQ2.Dyadic.AffineDeterminantCertificate"
def numericsRoot : String := "GQ2.Dyadic.standardNumerics"
def statementKind : String := "field_statement_identity"

def scopeNote : String :=
  "Ledger item 9 only: the wiring, the two-clause structure and the Gauss multipliers of the L/N0/Npc affine determinant certificate. No coefficient module, marking, field, resolver, eta or source certificate is selected."

def warningNote : String :=
  "AffineDeterminantCertificate is a Prop, so this display is NOT a rendering of the phase-cover proof and no formula is substituted for one. Lean has definitional proof irrelevance, so a field binding certifies that the producer proves exactly the statement the record's determinant field demands, at the record's own parameters, and NOT that the record was built from that proof term. The clause statements themselves remain in the packet's stored proofs transcript."

def hashScopeNote : String :=
  "Identity of the serialized wiring, clause structure and Gauss multiplier sign and exponent at the stated discrete parameters. It is not a hash of any proof."

/-- One Gauss multiplier: the sign at this degree, computed from the `rfl` formula, and the
factor the half-dimension `m` is multiplied by in the exponent of two. -/
def multiplierJson (bridge : String) (sign : ℤ) (degreeFactor : ℕ) : String :=
  "{\"bridge\":" ++ jsonString bridge ++ ",\"degree_factor\":" ++ natToString degreeFactor ++
    ",\"exponent\":" ++ jsonString "degree_factor * m" ++ ",\"sign\":" ++ intToString sign ++ "}"

def clauseJson (position : ℕ) (id multiplier role headCondition : String) : String :=
  "{\"head_condition\":" ++ jsonString headCondition ++ ",\"id\":" ++ jsonString id ++
  ",\"multiplier\":" ++ jsonString multiplier ++ ",\"position\":" ++ natToString position ++
  ",\"role\":" ++ jsonString role ++ "}"

def chain : List String :=
  [ clauseJson 1 "gauss_unramified" "gauss_unram"
      "At every nonzero radical line of a simple nontrivial block enrichment, the Gauss-Z residue of the source boundary map equals the unramified Gauss multiplier at the block's half-dimension."
      "the frame element at the tame tau acts trivially on the head quotient"
  , clauseJson 2 "gauss_ramified" "gauss_ram"
      "At the same lines, with the opposite head condition, the residue equals the ramified Gauss multiplier at the block's half-dimension."
      "the frame element at the tame tau moves some vector of the head quotient" ]

def numericsJson (n : ℕ) : String :=
  "{\"gauss_ram\":" ++ multiplierJson (bridgeRoot ++ "standardNumerics_gaussRam") 1 n ++
  ",\"gauss_unram\":" ++
    multiplierJson (bridgeRoot ++ "standardNumerics_gaussUnram") ((-1 : ℤ) ^ n) n ++
  ",\"half_dimension\":" ++ jsonString "m, with block order 2^(2m) and 1 <= m" ++
  ",\"record\":" ++ jsonString numericsRoot ++ "}"

def consumerJson (binding field record supply : String) (degree : ℕ) : String :=
  "{\"binding\":" ++ jsonString binding ++ ",\"binding_kind\":" ++ jsonString statementKind ++
  ",\"field\":" ++ jsonString field ++ ",\"record\":" ++ jsonString record ++
  ",\"record_degree\":" ++ natToString degree ++ ",\"supply\":" ++ jsonString supply ++ "}"

def producerJson (declaration scope : String) (degree : ℕ) (viaField : String) : String :=
  "{\"declaration\":" ++ jsonString declaration ++ ",\"degree\":" ++ natToString degree ++
  ",\"scope\":" ++ jsonString scope ++ ",\"via_field\":" ++ viaField ++ "}"

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
    (producerJson "GQ2.Dyadic.LSquare.determinantResidue_lSq_pow"
      "q = 2^f with f odd, which is narrower than the alpha and q conditions the even families use"
      (2*h+1) (jsonString (bridgeRoot ++ "lDeterminant_leaves")))
    (consumerJson (bridgeRoot ++ "lDeterminant_field") "determinant"
      "GQ2.Dyadic.LSquare.wordCertificateRN_lSq_of_actionImage"
      "analytic_leaves_record_field" (2*h+1))

def n0Payload (h q : ℕ) : String :=
  payload "N0" (2+2*h) (structuralLN h q)
    (producerJson
      "GQ2.Dyadic.Instances.WordPhaseCompactNFinal.wPcN_affineDeterminantCertificate"
      "2 <= alpha, q nonzero and Even q" (2+2*h) "null")
    (consumerJson (bridgeRoot ++ "n0Determinant_field") "determinant"
      "GQ2.Dyadic.Instances.WordPhaseCompactNFinal.wPcNWordCertificateRN" "theorem" (2+2*h))

def npcPayload (h q r : ℕ) : String :=
  payload "Npc" (2+2*h) (structuralNpc h q r)
    (producerJson
      "GQ2.Dyadic.Instances.NpcDeterminantFinal.npcAffineDeterminantCertificate"
      "2 <= alpha, q nonzero, Even q, and an exact NpcDisplayFor for the semantic unit"
      (2+2*h) "null")
    (consumerJson (bridgeRoot ++ "npcDeterminant_field") "determinant"
      "GQ2.Dyadic.Instances.NpcDeterminantFinal.npcWordCertificateRN" "theorem" (2+2*h))

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
  IO.println ("W363_LN_COVER_JSON=" ++ envelope p)

#print axioms standardNumerics_gaussUnram
#print axioms standardNumerics_gaussRam
#print axioms lDeterminant_field
#print axioms lDeterminant_leaves
#print axioms n0Determinant_field
#print axioms npcDeterminant_field
#print axioms exportMain

end GQ2.Dyadic.W363LNCover

def main (args : List String) : IO Unit := GQ2.Dyadic.W363LNCover.exportMain args
