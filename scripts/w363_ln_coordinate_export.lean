/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu
-/
import GQ2.Dyadic.Instances.GammaLGraphNormalForm
import GQ2.Dyadic.Instances.WordPhaseModel
import GQ2.Dyadic.Instances.NpcUnramifiedComparison
import GQ2.Dyadic.Instances.NpcRamifiedComparisonBase
import GQ2.Dyadic.Word.Export

/-!
# STAGED serializer for the L/N0/Npc change of variables (ledger item 8)

This is an exporter driver, not a library module: it carries a global `main` and stays
outside `GQ2.lean`, like the other W361/W362/W363 export executables.

**Item 8 splits, and only one half is reachable from an exporter lane.**

* The **change of variables** is a genuine `Equiv` with an explicit `toFun` and `invFun`, so
  it is data, and the bindings below are `rfl` against the `Equiv`'s own fields. That is the
  `record_target` strength of items 3, 4 and 5, and it is the strongest bridge any of the
  six W363 exporters gets outside the Fox layer.
* The **quadratic normal form record** itself, `SourceOddHessian`, is a different matter. The
  records that build it (`LHessianCertificates.unramifiedHessian` and `.ramifiedHessian`,
  `CompactNHessianCertificates.*`, `NpcHessianCertificates.*`) take a descent datum, a factor
  set, a projection, a coefficient module with its topology and action, a simplicity
  hypothesis and a cardinality. A `rfl` signature theorem against such a record requires
  instantiating all of it, which means **selecting a coefficient module, which this lane is
  forbidden to do**. Those records are therefore named in the artifact and explicitly marked
  as carrying no binding here.

The content worth publishing is the shape of the change. All four are the same handle
regrouping, `Fin h x Fin 2 -> A` to `Fin h -> A x A` through `finTwoProdAddEquiv`; what
differs is the head. L carries **one** head coordinate and leaves it alone. N0 carries
**two** and leaves both alone. Both Npc sectors carry two and **replace the first by its
image under the normal-form operator Phi**, which is exactly the "change of variables" the
ledger item is named for; the other three are rebracketings.

Scope. No coefficient module, marking, field, resolver, `eta` or source certificate is
selected: every theorem below is quantified over the coefficient group. This is not an
approved appendix, manifest entry, gate or release.
-/

namespace GQ2.Dyadic.W363LNCoordinate

open GQ2 GQ2.Dyadic.Instances
open GQ2.Dyadic.Export (jsonString natToString)

/-! ## Signature theorems: the exported components ARE the `Equiv`'s own fields

Each is `rfl` against `toFun` or `invFun`. -/

section Coordinates
variable {h : ℕ} {A : Type} [AddCommGroup A]

/-- **L.** One head coordinate, carried through unchanged; the handle coordinates are
regrouped into endpoint pairs. -/
theorem lCoords_toFun (p : A × (Fin h × Fin 2 → A)) :
    LSquare.lSqPhaseCoordsEquiv h A p
      = (p.1, fun j => finTwoProdAddEquiv (fun k => p.2 (j, k))) := rfl

theorem lCoords_invFun (p : A × (Fin h → A × A)) :
    (LSquare.lSqPhaseCoordsEquiv h A).symm p
      = (p.1, fun jk => (finTwoProdAddEquiv.symm (p.2 jk.1)) jk.2) := rfl

/-- **N0.** Two head coordinates, both carried through unchanged. -/
theorem n0Coords_toFun (p : A × A × (Fin h × Fin 2 → A)) :
    WordPhaseModel.wPmCompactCoordsEquiv h A p
      = ((p.1, p.2.1), fun j => finTwoProdAddEquiv (fun k => p.2.2 (j, k))) := rfl

theorem n0Coords_invFun (p : (A × A) × (Fin h → A × A)) :
    (WordPhaseModel.wPmCompactCoordsEquiv h A).symm p
      = (p.1.1, p.1.2, fun jk => (finTwoProdAddEquiv.symm (p.2 jk.1)) jk.2) := rfl

/-- **Npc, unramified.** Two head coordinates, the first replaced by its image under the
normal-form operator `Phi`. This is the genuine change of variables. -/
theorem npcUnramCoords_toFun (Phi : A ≃+ A) (r : A × A × (Fin h × Fin 2 → A)) :
    NpcUnramifiedComparison.wPnpcPhiCoordsEquiv h A Phi r
      = ((Phi r.1, r.2.1), fun j => finTwoProdAddEquiv (fun k => r.2.2 (j, k))) := rfl

theorem npcUnramCoords_invFun (Phi : A ≃+ A) (p : (A × A) × (Fin h → A × A)) :
    (NpcUnramifiedComparison.wPnpcPhiCoordsEquiv h A Phi).symm p
      = (Phi.symm p.1.1, p.1.2, fun jk => (finTwoProdAddEquiv.symm (p.2 jk.1)) jk.2) := rfl

/-- **Npc, ramified.** The same change of variables on the twisted coordinates. -/
theorem npcRamCoords_toFun (Phi : A ≃+ A) (r : A × A × (Fin h × Fin 2 → A)) :
    NpcRamifiedComparisonBase.wPnpcRamifiedCoordsEquiv h A Phi r
      = ((Phi r.1, r.2.1), fun j => finTwoProdAddEquiv (fun k => r.2.2 (j, k))) := rfl

theorem npcRamCoords_invFun (Phi : A ≃+ A) (p : (A × A) × (Fin h → A × A)) :
    (NpcRamifiedComparisonBase.wPnpcRamifiedCoordsEquiv h A Phi).symm p
      = (Phi.symm p.1.1, p.1.2, fun jk => (finTwoProdAddEquiv.symm (p.2 jk.1)) jk.2) := rfl

end Coordinates

/-! ## Canonical JSON serialization

Keys are emitted in ASCII order so that the bytes agree with Python's
`json.dumps(..., sort_keys=True, separators=(",",":"))` used by the checker. -/

def schema : String := "gq2.w363.ln-coordinate.v1.staged"
def hashDomain : String := "GQ2-W363-LN-COORDINATE\x00"
def bridgeRoot : String := "GQ2.Dyadic.W363LNCoordinate."
def recordKind : String := "record_target"
def unboundKind : String := "named_but_unbound"

def scopeNote : String :=
  "Ledger item 8 only: the change of variables to the quadratic normal form, as the explicit components of the tree's own Equiv values. No coefficient module, marking, field, resolver, eta or source certificate is selected: every signature theorem is quantified over the coefficient group."

def warningNote : String :=
  "Only the change of variables is bound here. The quadratic normal form RECORD itself, SourceOddHessian, is not: the declarations that build it take a descent datum, a factor set, a projection, a coefficient module with its topology and action, a simplicity hypothesis and a cardinality, so a rfl signature theorem against one would require selecting a coefficient module, which this lane is forbidden to do. Those records are named below with the bridge kind named_but_unbound, and naming is not binding."

def hashScopeNote : String :=
  "Identity of the serialized coordinate components and the named normal-form records at the stated handle rank. It is not a hash of any proof, and it says nothing about the normal-form records' content."

def headNote : String :=
  "All four sectors share one handle regrouping, from Fin h times Fin 2 into A to Fin h into A times A, through finTwoProdAddEquiv. What differs is the head: L carries one head coordinate and leaves it alone, N0 carries two and leaves both alone, and both Npc sectors carry two and replace the first by its image under the normal-form operator Phi. Only the Npc sectors are a change of variables in the ledger item's sense; the other two are rebracketings."

def bracket (xs : List String) : String := "[" ++ String.intercalate "," xs ++ "]"

def sectorJson (name equiv forward inverse headTransform : String) (heads : ℕ)
    (records : List String) : String :=
  "{\"equiv\":" ++ jsonString equiv ++
  ",\"forward_bridge\":" ++ jsonString forward ++
  ",\"head_coordinates\":" ++ natToString heads ++
  ",\"head_transform\":" ++ jsonString headTransform ++
  ",\"inverse_bridge\":" ++ jsonString inverse ++
  ",\"normal_form_records\":" ++ bracket (records.map jsonString) ++
  ",\"sector\":" ++ jsonString name ++ "}"

def LGN : String := "GQ2.Dyadic.LSquare."
def WPM : String := "GQ2.Dyadic.Instances.WordPhaseModel."
def NUC : String := "GQ2.Dyadic.Instances.NpcUnramifiedComparison."
def NRC : String := "GQ2.Dyadic.Instances.NpcRamifiedComparisonBase."
def LHC : String := "GQ2.Dyadic.Instances.LHessianCertificates."
def CNH : String := "GQ2.Dyadic.Instances.CompactNHessianCertificates."
def NHC : String := "GQ2.Dyadic.Instances.NpcHessianCertificates."

def lSectors : List String :=
  [ sectorJson "graph_normal_form" (LGN ++ "lSqPhaseCoordsEquiv")
      (bridgeRoot ++ "lCoords_toFun") (bridgeRoot ++ "lCoords_invFun")
      "identity" 1
      [LHC ++ "unramifiedHessian", LHC ++ "ramifiedHessian"] ]

def n0Sectors : List String :=
  [ sectorJson "compact_normal_form" (WPM ++ "wPmCompactCoordsEquiv")
      (bridgeRoot ++ "n0Coords_toFun") (bridgeRoot ++ "n0Coords_invFun")
      "identity" 2
      [CNH ++ "compactNUnramifiedHessian", CNH ++ "compactNRamifiedHessian"] ]

def npcSectors : List String :=
  [ sectorJson "unramified_full_offset" (NUC ++ "wPnpcPhiCoordsEquiv")
      (bridgeRoot ++ "npcUnramCoords_toFun") (bridgeRoot ++ "npcUnramCoords_invFun")
      "phi" 2 [NHC ++ "npcUnramifiedHeadHessian"]
  , sectorJson "ramified_full_offset" (NRC ++ "wPnpcRamifiedCoordsEquiv")
      (bridgeRoot ++ "npcRamCoords_toFun") (bridgeRoot ++ "npcRamCoords_invFun")
      "phi" 2 [NHC ++ "nonempty_npcRamifiedHeadHessian"] ]

def payload (family : String) (h : ℕ) (structural : String) (sectors : List String) : String :=
  "{\"application_scope\":" ++ jsonString scopeNote ++ "," ++
  "\"family\":" ++ jsonString family ++ "," ++
  "\"handle_regrouping\":{\"bridge_kind\":" ++ jsonString recordKind ++
    ",\"planes\":" ++ natToString h ++ ",\"via\":\"finTwoProdAddEquiv\"}," ++
  "\"hash_scope\":" ++ jsonString hashScopeNote ++ "," ++
  "\"head_note\":" ++ jsonString headNote ++ "," ++
  "\"record_binding\":" ++ jsonString unboundKind ++ "," ++
  "\"schema\":" ++ jsonString schema ++ "," ++
  "\"sectors\":" ++ bracket sectors ++ "," ++
  "\"structural\":" ++ structural ++ "," ++
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
      | some h, some q => pure (payload "L" h (structuralLN h q) lSectors)
      | _, _ => throw (IO.userError "L H Q: H and Q must be natural numbers")
    | ["N0", hs, qs] => match hs.toNat?, qs.toNat? with
      | some h, some q => pure (payload "N0" h (structuralLN h q) n0Sectors)
      | _, _ => throw (IO.userError "N0 H Q: H and Q must be natural numbers")
    | ["Npc", hs, qs, rs] => match hs.toNat?, qs.toNat?, rs.toNat? with
      | some h, some q, some r => pure (payload "Npc" h (structuralNpc h q r) npcSectors)
      | _, _, _ => throw (IO.userError "Npc H Q R: H, Q and R must be natural numbers")
    | _ => throw (IO.userError "usage: L H Q | N0 H Q | Npc H Q R")
  IO.println ("W363_LN_COORDINATE_JSON=" ++ envelope p)

#print axioms lCoords_toFun
#print axioms lCoords_invFun
#print axioms n0Coords_toFun
#print axioms n0Coords_invFun
#print axioms npcUnramCoords_toFun
#print axioms npcUnramCoords_invFun
#print axioms npcRamCoords_toFun
#print axioms npcRamCoords_invFun
#print axioms exportMain

end GQ2.Dyadic.W363LNCoordinate

def main (args : List String) : IO Unit := GQ2.Dyadic.W363LNCoordinate.exportMain args
