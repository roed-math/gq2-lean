/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu
-/
import GQ2.Dyadic.Instances.GammaLReconstruction
import GQ2.Dyadic.Instances.WordPhaseCompactNFinal
import GQ2.Dyadic.Instances.NpcCandidateRN
import GQ2.Dyadic.Instances.NpcDeterminantFinal
import GQ2.Dyadic.Word.Export

/-!
# STAGED serializer for the L/N0/Npc two specializations (ledger item 2)

This is an exporter driver, not a library module: it carries a global `main` and stays
outside `GQ2.lean`, like the other W361/W362/W363 export executables.

**Item 2 splits, and the split is the content.** The two specializations are in different
states in the tree and the artifact keeps them apart.

* The **pro-2 specialization** is a syntactic identity between `PWord` values. The tree
  states it at N0 and Npc as a single whole-word equation (`pro2_nCompact`, `pro2_npcW`);
  at L it states the core list (`pro2_lSqCore`) and the evaluated form
  (`eval_pro2_lSqW`), and the whole-word syntactic equation is assembled here from the core
  list and the handle tail. Each family's factor list is restated in the driver and
  discharged by the tree's own theorem, so a wrong factor list does not compile. That is the
  `restated_identity` bridge kind item 7 introduced.
* The **tame specialization** is a `Prop` carried as the `tameSpecialization` field of the
  word certificate record. As in items 6 and 9, proof irrelevance makes the field binding a
  **statement identity**, and the bridge kind is `field_statement_identity`.

**What Gate C keeps.** The pro-2 map removes the `tau` letter and collapses every `omega2`
power; it does **not** collapse the profinite `eta-hat` power or the integer `2^r`
conjugator at Npc, and the Npc correction block stays folded in the tree's own statement
because what matters about it is its value, not its pro-2 syntax. The factor descriptors say
so rather than expanding anything the Lean leaves folded.

**What this exporter does not touch.** Ledger item 2 is also where the three field-selection
adapters `FieldFamilyCampaignBoundary.hasSelectedRowResidualRN_{l,n0,npc}` are pinned. Those
are **not** standard-three: each carries four documented standing arithmetic and reciprocity
inputs, and W362 pins them in their own class and prints their full axiom list. Nothing here
touches them, nothing here weakens that class, and the two specializations below are not a
statement about the field scope.

Scope. No coefficient module, marking, field, resolver, `eta` or source certificate is
selected. This is not an approved appendix, manifest entry, gate or release.
-/

namespace GQ2.Dyadic.W363LNSpecialization

open GQ2 GQ2.Dyadic.Words
open GQ2.Dyadic.Export (jsonString natToString)

/-! ## Signature theorems, part 1: the pro-2 specialization as a factor list -/

/-- The L handle tail is pro-2 invariant. The tree proves this for the single `handlesW`
block; the tail is that block or nothing, so the list form is a case split. It is the one
step the L whole-word equation needs that the tree does not already state. -/
theorem pro2_lSqHandleTail (h : ℕ) :
    (Words.LSq.handleTail h).map pro2 = Words.LSq.handleTail h := by
  cases h with
  | zero => rfl
  | succ k => simp [Words.LSq.handleTail, Words.LSq.pro2_handlesW]

/-- **L.** The whole-word pro-2 specialization, assembled from the tree's core-list equation
and the handle tail. The `a`-letter has become `x0^(-3) * 1`, whose trailing `1` is the
collapsed `tau`, and the commutator block's conjugator has become the plain `sigma`. -/
theorem lPro2_shape (h : ℕ) :
    pro2 (Words.LSq.lSqW h) = PWord.prodList
      ([.inv (.conj (.gen (Words.LSq.coreLetter h 0)) (.gen .sigma)),
        PWord.prodList [.zpow (.gen (Words.LSq.coreLetter h 0)) (-3), .one],
        .zpow (.gen (Words.LSq.coreLetter h 1)) 2,
        .comm (.gen (Words.LSq.coreLetter h 1))
          (.conj (.gen (Words.LSq.coreLetter h 1)) (.gen .sigma))]
       ++ Words.LSq.handleTail h) := by
  rw [Words.LSq.lSqW, pro2_prodList, List.map_append, Words.LSq.pro2_lSqCore,
    pro2_lSqHandleTail]

/-- **N0.** The tree's own whole-word equation, restated as the factor list the artifact
serializes. -/
theorem n0Pro2_shape (alpha h : ℕ) :
    pro2 (nCompactW alpha h) = PWord.prodList
      [.zpow (.gen (Words.coreLetter h 0)) (2 + 2 ^ alpha),
       .comm (.gen (Words.coreLetter h 0)) (.gen (Words.coreLetter h 1)),
       .inv (.conj (.gen (Words.coreLetter h 2)) (.gen .sigma)),
       PWord.prodList [.gen (Words.coreLetter h 2), .one],
       handlesW h] :=
  pro2_nCompact alpha h

/-- **Npc.** The tree's own whole-word equation. The second factor keeps the profinite
`eta-hat` power, the third keeps the integer `2^r` conjugator, and the correction block stays
folded, all exactly as Gate C leaves them. -/
theorem npcPro2_shape (alpha r h : ℕ) (e : EtaData) :
    pro2 (Words.Npc.npcW alpha r h e) = PWord.prodList
      [.zpow (.gen (Words.coreLetter h 0)) (2 + 2 ^ alpha),
       .comm (.gen (Words.coreLetter h 0)) (Words.Npc.aW h e),
       .inv (.conj (.gen (Words.coreLetter h 2))
         (PWord.prodList [.gen (Words.coreLetter h 1), Words.Npc.bW h r])),
       PWord.prodList [.gen (Words.coreLetter h 2), .one],
       pro2 (Words.Npc.eBlockW h r e),
       handlesW h] :=
  Words.Npc.pro2_npcW alpha r h e

/-! ## Signature theorems, part 2: the tame specialization is the record's own field

Statement identity, not proof identity: `TameSpecializes` is a `Prop`. -/

/-- **L.** -/
theorem lTame_field {h q : ℕ} (hq2 : 2 ≤ q) (hqe : Even q)
    (A : LSquare.LSquareAnalyticLeavesRN h q hq2 hqe) :
    (LSquare.wordCertificateRN_lSq_of_actionImage hq2 hqe A).tameSpecialization
      = LSquare.lCanonicalTameSpecialization h q hq2 hqe := rfl

/-- **N0.** -/
theorem n0Tame_field (alpha h q : ℕ) (halpha : 2 ≤ alpha) (hq0 : q ≠ 0) (hqe : Even q) :
    (Instances.WordPhaseCompactNFinal.wPcNWordCertificateRN alpha h q halpha hq0
        hqe).tameSpecialization
      = genCertNTameSpecializes alpha h q hq0 hqe := rfl

/-- **Npc.** Bound at the unconditional record, which needs no determinant argument. -/
theorem npcTame_field (alpha r h q : ℕ) {eta : ℤ_[2]ˣ} (d : NpcDisplayFor eta)
    (halpha : 2 ≤ alpha) (hq0 : q ≠ 0) (hqe : Even q) :
    (Instances.NpcDeterminantFinal.npcWordCertificateRN alpha r h q d halpha hq0
        hqe).tameSpecialization
      = Instances.NpcCandidateRN.npcCandidate_tameSpecializes alpha r h q d hq0 hqe := rfl

/-! ## Canonical JSON serialization

Keys are emitted in ASCII order so that the bytes agree with Python's
`json.dumps(..., sort_keys=True, separators=(",",":"))` used by the checker. -/

def schema : String := "gq2.w363.ln-specialization.v1.staged"
def hashDomain : String := "GQ2-W363-LN-SPECIALIZATION\x00"
def bridgeRoot : String := "GQ2.Dyadic.W363LNSpecialization."
def restatedKind : String := "restated_identity"
def statementKind : String := "field_statement_identity"

def scopeNote : String :=
  "Ledger item 2 only: the pro-two specialization as a factor list and the tame specialization as a record field. No coefficient module, marking, field, resolver, eta or source certificate is selected."

def warningNote : String :=
  "The two halves of item 2 are NOT in the same state and are not presented as if they were. The pro-two half is a syntactic identity between PWord values, restated here and discharged by the tree's own theorem, so a wrong factor list does not compile; the factor descriptions themselves are prose. The tame half is a Prop carried as a record field, and proof irrelevance makes its binding a statement identity, not proof identity. Separately: item 2 is also where the three field-selection adapters are pinned, and those are NOT standard-three, each carrying four documented standing arithmetic and reciprocity inputs. Nothing in this artifact touches them or weakens that class."

def hashScopeNote : String :=
  "Identity of the serialized factor list, its descriptions and the two bindings at the stated discrete parameters. It is not a hash of any PWord value."

def gateNote : String :=
  "Gate C removes the tau letter and collapses every omega2 power. It does NOT collapse the profinite eta-hat power or the integer two-power conjugator at Npc, and the Npc correction block stays folded in the tree's own statement because what matters about it is its value, not its pro-two syntax."

def factorJson (position : ℕ) (kind description : String) : String :=
  "{\"description\":" ++ jsonString description ++ ",\"kind\":" ++ jsonString kind ++
    ",\"position\":" ++ natToString position ++ "}"

def bracket (xs : List String) : String := "[" ++ String.intercalate "," xs ++ "]"

def proTwoJson (bridge source tail : String) (factors : List String) : String :=
  "{\"bridge\":" ++ jsonString bridge ++ ",\"bridge_kind\":" ++ jsonString restatedKind ++
  ",\"factors\":" ++ bracket factors ++ ",\"source\":" ++ jsonString source ++
  ",\"tail\":" ++ jsonString tail ++ "}"

def tameJson (binding producer record : String) : String :=
  "{\"binding\":" ++ jsonString binding ++ ",\"binding_kind\":" ++ jsonString statementKind ++
  ",\"field\":\"tameSpecialization\",\"producer\":" ++ jsonString producer ++
  ",\"record\":" ++ jsonString record ++ "}"

/-- The handle tail's description at this rank. It is genuinely empty at rank zero, which is
the certificate's own convention and not a simplification. -/
def tailText (h : ℕ) (invariance : String) : String :=
  if h = 0 then
    "the handle tail is EMPTY at this rank, which is the certificate's own convention and not a simplification (" ++ invariance ++ ")"
  else
    "the handle tail is one handles block of " ++ natToString h ++ " commutator planes at this rank (" ++ invariance ++ ")"

def lProTwo (h : ℕ) : String :=
  proTwoJson (bridgeRoot ++ "lPro2_shape")
    "GQ2.Dyadic.Words.LSq.pro2_lSqCore"
    (tailText h "pro-two invariant by GQ2.Dyadic.W363LNSpecialization.pro2_lSqHandleTail")
    [ factorJson 1 "inverse_conjugate" "the inverse sigma-conjugate of x0"
    , factorJson 2 "collapsed_a_letter" "x0 to the power minus three, times the unit that is the collapsed tau"
    , factorJson 3 "integer_power" "x1 squared"
    , factorJson 4 "commutator" "the commutator of x1 with its plain sigma-conjugate: the sigma2 conjugator has become sigma" ]

def n0ProTwo (h : ℕ) : String :=
  proTwoJson (bridgeRoot ++ "n0Pro2_shape")
    "GQ2.Dyadic.Words.pro2_nCompact"
    (tailText h "the handles block handlesW, pro-two invariant by GQ2.Dyadic.Words.pro2_handlesW")
    [ factorJson 1 "integer_power" "x0 to the power two plus two to the alpha"
    , factorJson 2 "commutator" "the commutator of x0 with x1"
    , factorJson 3 "inverse_conjugate" "the inverse sigma-conjugate of x2"
    , factorJson 4 "collapsed_tau" "x2 times the unit that is the collapsed tau" ]

def npcProTwo (h : ℕ) : String :=
  proTwoJson (bridgeRoot ++ "npcPro2_shape")
    "GQ2.Dyadic.Words.Npc.pro2_npcW"
    (tailText h "the handles block handlesW, pro-two invariant by GQ2.Dyadic.Words.pro2_handlesW")
    [ factorJson 1 "integer_power" "x0 to the power two plus two to the alpha"
    , factorJson 2 "commutator_with_eta_power"
        "the commutator of x0 with the profinite eta-hat power of sigma, which Gate C keeps"
    , factorJson 3 "inverse_conjugate_twisted"
        "the inverse conjugate of x2 by x1 times the integer two-power conjugator, which Gate C keeps"
    , factorJson 4 "collapsed_tau" "x2 times the unit that is the collapsed tau"
    , factorJson 5 "folded_block"
        "the correction block, left folded in the tree's own statement as the pro-two image of eBlockW" ]

def lTame : String :=
  tameJson (bridgeRoot ++ "lTame_field")
    "GQ2.Dyadic.LSquare.lCanonicalTameSpecialization"
    "GQ2.Dyadic.LSquare.wordCertificateRN_lSq_of_actionImage"

def n0Tame : String :=
  tameJson (bridgeRoot ++ "n0Tame_field")
    "GQ2.Dyadic.genCertNTameSpecializes"
    "GQ2.Dyadic.Instances.WordPhaseCompactNFinal.wPcNWordCertificateRN"

def npcTame : String :=
  tameJson (bridgeRoot ++ "npcTame_field")
    "GQ2.Dyadic.Instances.NpcCandidateRN.npcCandidate_tameSpecializes"
    "GQ2.Dyadic.Instances.NpcDeterminantFinal.npcWordCertificateRN"

def payload (family : String) (structural proTwo tame : String) : String :=
  "{\"application_scope\":" ++ jsonString scopeNote ++ "," ++
  "\"family\":" ++ jsonString family ++ "," ++
  "\"gate\":" ++ jsonString gateNote ++ "," ++
  "\"hash_scope\":" ++ jsonString hashScopeNote ++ "," ++
  "\"pro_two\":" ++ proTwo ++ "," ++
  "\"schema\":" ++ jsonString schema ++ "," ++
  "\"structural\":" ++ structural ++ "," ++
  "\"tame\":" ++ tame ++ "," ++
  "\"warning\":" ++ jsonString warningNote ++ "}"

def envelope (p : String) : String :=
  "{\"payload\":" ++ p ++ ",\"status\":\"STAGED\",\"template_hash\":" ++
    jsonString (Export.Sha256.hex (hashDomain ++ p)) ++ "}"

def structuralLN (h q : ℕ) : String :=
  "{\"h\":" ++ natToString h ++ ",\"q\":" ++ natToString q ++ "}"

def structuralNpc (h q r : ℕ) : String :=
  "{\"h\":" ++ natToString h ++ ",\"q\":" ++ natToString q ++ ",\"r\":" ++ natToString r ++ "}"

def exportMain (args : List String) : IO Unit := do
  let p ← match args with
    | ["L", hs, qs] => match hs.toNat?, qs.toNat? with
      | some h, some q => pure (payload "L" (structuralLN h q) (lProTwo h) lTame)
      | _, _ => throw (IO.userError "L H Q: H and Q must be natural numbers")
    | ["N0", hs, qs] => match hs.toNat?, qs.toNat? with
      | some h, some q => pure (payload "N0" (structuralLN h q) (n0ProTwo h) n0Tame)
      | _, _ => throw (IO.userError "N0 H Q: H and Q must be natural numbers")
    | ["Npc", hs, qs, rs] => match hs.toNat?, qs.toNat?, rs.toNat? with
      | some h, some q, some r =>
          pure (payload "Npc" (structuralNpc h q r) (npcProTwo h) npcTame)
      | _, _, _ => throw (IO.userError "Npc H Q R: H, Q and R must be natural numbers")
    | _ => throw (IO.userError "usage: L H Q | N0 H Q | Npc H Q R")
  IO.println ("W363_LN_SPECIALIZATION_JSON=" ++ envelope p)

#print axioms pro2_lSqHandleTail
#print axioms lPro2_shape
#print axioms n0Pro2_shape
#print axioms npcPro2_shape
#print axioms lTame_field
#print axioms n0Tame_field
#print axioms npcTame_field
#print axioms exportMain

end GQ2.Dyadic.W363LNSpecialization

def main (args : List String) : IO Unit := GQ2.Dyadic.W363LNSpecialization.exportMain args
