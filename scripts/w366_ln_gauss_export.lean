/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu
-/
import GQ2.Dyadic.Instances.GaussPhaseValues
import GQ2.Dyadic.Word.Export

/-!
# STAGED serializer for item 8's normal-form Gauss display (ledger item 8, second half)

This is an exporter driver, not a library module: it carries a global `main` and stays
outside `GQ2.lean`, like the other W361/W362/W363 export executables.

`scripts/w363_ln_coordinate_export.lean` exports item 8's **coordinate** half, whose bindings
are `rfl` against the change-of-variables `Equiv`'s own fields. Its normal-form half was left
`named_but_unbound`, because the Gauss sign and exponent the normal-form records establish on
the way were not named standalone theorems anywhere. `GQ2/Dyadic/Instances/GaussPhaseValues.lean`
names them. This driver wires the five item-8 sector rows to them.

Per row, two different bridge kinds, and the artifact keeps them apart:

* **the printed sign and the printed exponent**: `record_target`. Each is `rfl` against a
  field of `GaussValCell`, which is data with explicit fields, exactly as item 8's coordinate
  half is `rfl` against the `Equiv`'s own fields.
* **the value equation**: `restated_identity`. The carrier is a theorem, not a record. The
  theorems below restate `gaussSum <endpoint> = (<cell>).value m` through the named cell and
  discharge the restatement by the tree's own theorem, so **a wrong cell does not compile**.

What this driver does **not** change: the normal-form records `SourceOddHessian`,
`SourceCompactHessian` and `SourceWallHessian` are still `named_but_unbound`. They are
unreachable without instantiating a coefficient module, which no exporter lane may do. The
cells reach the same displayed numbers through theorems about the *endpoint phase function*,
which is quantified over the coefficient group, so the cells and the records carry different
kinds inside one artifact and the artifact says so.

Scope. No coefficient module, marking, field, resolver, `eta` or source certificate is
selected: every theorem below is quantified over them. This is not an approved appendix,
manifest entry, gate or release.
-/

namespace GQ2.Dyadic.W366LNGauss

open GQ2 GQ2.Dyadic.Instances.GaussPhaseValues
open GQ2.Dyadic.Export (jsonString natToString intToString)

/-! ## Signature theorems, part one: the printed sign and the printed exponent

Each is `rfl` against a field of `GaussValCell`. -/

section Cells
variable (h : ℕ)

/-- **L unramified.** Printed sign `-1`. -/
theorem lUnramSign : (gaussValLUnramCell h).sign = -1 := rfl

/-- **L unramified.** Printed exponent degree `2 * h + 1`. -/
theorem lUnramDegree : (gaussValLUnramCell h).degree = 2 * h + 1 := rfl

/-- **L ramified.** Printed sign `+1`. -/
theorem lRamSign : (gaussValLRamCell h).sign = 1 := rfl

/-- **L ramified.** Printed exponent degree `2 * h + 1`. -/
theorem lRamDegree : (gaussValLRamCell h).degree = 2 * h + 1 := rfl

/-- **N0, and both `Npc` sectors.** Printed sign `+1`: one cell serves the three
even-degree rows. -/
theorem compactSign : (gaussValCompactCell h).sign = 1 := rfl

/-- **N0, and both `Npc` sectors.** Printed exponent degree `2 * h + 2`. -/
theorem compactDegree : (gaussValCompactCell h).degree = 2 * h + 2 := rfl

/-- The displayed integer is the cell's two printed fields, and nothing else. -/
theorem cellValue (c : GaussValCell) (m : ℕ) : c.value m = c.sign * 2 ^ (m * c.degree) := rfl

end Cells

/-! ## Signature theorems, part two: the value equation, restated through the cell

The carrier is a theorem, not a record, so these are `restated_identity` and not
`record_target`: each restates the endpoint's Gauss value through the named cell and is
discharged by the tree's own theorem. A wrong cell does not compile. -/

noncomputable section Values

open GQ2 GQ2.SectionEight GQ2.FoxH GQ2.QuadraticFp2
open SectionSeven AffineTLift CentralObstruction ContCoh
open GQ2.Dyadic GQ2.Dyadic.Count GQ2.Dyadic.LSquare
open GQ2.Dyadic.Words GQ2.Dyadic.Words.LSq
open GQ2.Dyadic.Certificates
open Instances.WordPhaseOddCertificates Instances.LPhaseAdditiveNormal
open Instances.LHessianCertificates

section LRows

variable {h q : ℕ}
  {Bg : Type} [Group Bg] [Finite Bg] [TopologicalSpace Bg] [DiscreteTopology Bg]
  {D : RadicalCoverData Bg} {DD : DescData D}
  (rho : ContinuousMonoidHom ((gamma h q : Type)) (Bg ⧸ D.M))
  [TopologicalSpace DD.Vmod] [IsTopologicalAddGroup DD.Vmod] [DiscreteTopology DD.Vmod]
  [TopologicalSpace DD.C0] [DiscreteTopology DD.C0]
  [DistribMulAction ((gamma h q : Type)) DD.Vmod]
  [ContinuousSMul ((gamma h q : Type)) DD.Vmod]
  {Cbar : Type} [Group Cbar] [DistribMulAction Cbar DD.Vmod]
  (base : FactorSet Cbar DD.Vmod) (hbase : IsEquivariantFactorSet DD.qbar base)
  (pi : DD.C0 →* Cbar) (hpi : ∀ (cc : DD.C0) (v : DD.Vmod), cc • v = pi cc • v)
  (hf : ∀ a b : DD.Vmod, DD.dat.f a b = base.f a b)
  (hm : ∀ (cc : DD.C0) (v : DD.Vmod), DD.dat.m cc v = base.m (pi cc) v)
  (hcompat : ∀ (g : (gamma h q : Type)) (v : DD.Vmod), g • v = rho0 DD rho g • v)

local instance : TopologicalSpace (ZMod 2) := ⊥
local instance : DiscreteTopology (ZMod 2) := ⟨rfl⟩
local instance : Fintype DD.Vmod := Fintype.ofFinite _
local instance : Finite (SectionSix.SemiProd DD.C0 DD.Vmod) :=
  inferInstanceAs (Finite (DD.Vmod × DD.C0))
local instance : DistribMulAction ((gamma h q : Type)) (ZMod 2) := scalarActionZmodTwo _
local instance : ContinuousSMul ((gamma h q : Type)) (ZMod 2) :=
  scalarActionZmodTwo_continuousSMul _

include base hbase hpi hf hm hcompat in
/-- **Row 1, `graph_normal_form` unramified.** The `L` unramified endpoint's Gauss value,
restated through `gaussValLUnramCell` and discharged by the tree's own theorem. -/
theorem lUnramValue
    (hsimple : IsSimpleModTwo (gamma h q : Type) DD.Vmod)
    (hqe : Even q) (m : ℕ) (hm1 : 1 ≤ m) (hcard : Nat.card DD.Vmod = 2 ^ (2 * m))
    (G : LUnramifiedHeadData (DD := DD) rho pi) :
    QuadraticFp2.gaussSum (lSqWallHandlePhase DD.qbar (headOperator rho pi) h)
      = (gaussValLUnramCell h).value m :=
  gaussValLUnramifiedCell rho base hbase pi hpi hf hm hcompat hsimple hqe m hm1 hcard G

include base hbase hpi hf hm hcompat in
/-- **Row 2, `graph_normal_form` ramified.** The `L` ramified endpoint's Gauss value,
restated through `gaussValLRamCell` and discharged by the tree's own theorem. -/
theorem lRamValue [Finite Cbar]
    (hqe : Even q) (m : ℕ) (hcard : Nat.card DD.Vmod = 2 ^ (2 * m))
    (G : LRamifiedHeadData (DD := DD) rho pi)
    (S : LRamifiedSourceArfData rho (scalarActionZmodTwo_triv _) hcompat) :
    QuadraticFp2.gaussSum (lSqWallHandlePhase DD.qbar (headOperator rho pi) h)
      = (gaussValLRamCell h).value m :=
  gaussValLRamifiedCell rho base hbase pi hpi hf hm hcompat hqe m hcard G S

end LRows

section CompactRow

open Instances.WordPhase

variable {V : Type} [AddCommGroup V] [Fintype V] {q : V → ZMod 2}

/-- **Row 3, `compact_normal_form`, both branches.** The compact endpoint's Gauss value,
restated through `gaussValCompactCell`. One cell serves both compact branches because at
even degree the unramified and the ramified target are the same integer. -/
theorem compactValue (hq : IsQuadraticFp2 q) (hns : Nonsingular q) {m : ℕ}
    (hcard : Fintype.card V = 2 ^ (2 * m)) (h : ℕ) :
    QuadraticFp2.gaussSum (wPhCompactWallHandlePhase q h)
      = (gaussValCompactCell h).value m :=
  gaussValCompactCellEq hq hns hcard h

end CompactRow

section WallRows

open Instances.WordPhaseWallHandleCertificates

variable {V : Type} [AddCommGroup V] [Fintype V] {d0 q : V → ZMod 2}

/-- **Rows 4 and 5, `unramified_full_offset` and `ramified_full_offset`.** The `Npc`
full-offset endpoint's Gauss value, restated through the same compact cell. Both `Npc` rows
share one endpoint and one cell; the sign does not depend on the projected diagonal `d0`. -/
theorem npcValue (hd : IsQuadraticFp2 d0) (hq : IsQuadraticFp2 q) (hns : Nonsingular q)
    {m : ℕ} (hcard : Fintype.card V = 2 ^ (2 * m)) (h : ℕ) :
    QuadraticFp2.gaussSum (wallHandlePhase d0 q h) = (gaussValCompactCell h).value m :=
  gaussValNpcCellEq hd hq hns hcard h

end WallRows

end Values

/-! ## Canonical JSON serialization

Keys are emitted in ASCII order so that the bytes agree with Python's
`json.dumps(..., sort_keys=True, separators=(",",":"))` used by the checker. -/

def schema : String := "gq2.w366.ln-gauss.v1.staged"
def hashDomain : String := "GQ2-W366-LN-GAUSS\x00"
def bridgeRoot : String := "GQ2.Dyadic.W366LNGauss."
def recordKind : String := "record_target"
def restatedKind : String := "restated_identity"
def unboundKind : String := "named_but_unbound"

def GPV : String := "GQ2.Dyadic.Instances.GaussPhaseValues."
def LSQ : String := "GQ2.Dyadic.LSquare."
def WPH : String := "GQ2.Dyadic.Instances.WordPhase."
def WWH : String := "GQ2.Dyadic.Instances.WordPhaseWallHandleCertificates."
def LHC : String := "GQ2.Dyadic.Instances.LHessianCertificates."
def CNH : String := "GQ2.Dyadic.Instances.CompactNHessianCertificates."
def NHC : String := "GQ2.Dyadic.Instances.NpcHessianCertificates."

def scopeNote : String :=
  "Ledger item 8, normal-form half only: the Gauss sign and exponent each item-8 sector row prints, as the fields of the tree's own GaussValCell values, plus the value equation restated through the cell. No coefficient module, marking, field, resolver, eta or source certificate is selected: every signature theorem is quantified over them."

def warningNote : String :=
  "Two different bridge kinds live in one artifact and may not be conflated. The printed sign and the printed exponent are record_target: rfl against a field of GaussValCell. The value equation is restated_identity: its carrier is a theorem, not a record, and the driver restates it through the named cell so that a wrong cell does not compile. The normal-form RECORDS remain named_but_unbound, exactly as w363_ln_coordinate_export left them: SourceOddHessian, SourceCompactHessian and SourceWallHessian are still unreachable without instantiating a coefficient module, which this lane is forbidden to do. Naming is not binding."

def hashScopeNote : String :=
  "Identity of the serialized display cells, their bridges and the named normal-form records at the stated handle rank. It is not a hash of any proof, and it says nothing about the normal-form records' content."

def cellNote : String :=
  "Each row's displayed integer is the cell's two printed fields and nothing else: value c m = c.sign * 2 ^ (m * c.degree), by rfl. There are three cells and five rows because the L branches differ in sign while the three even-degree rows share one cell: at even degree the unramified and the ramified target are the same integer."

def todoSecondSignRoute : String :=
  "TODO: only the L rows have a second, independent record_target route for the printed sign, through LHessianCertificates.unramifiedHessian_baseSign and .ramifiedHessian_baseSign. N0 and Npc have no named baseSign theorem: the fact holds by rfl and is supplied inline as a rfl argument at the certificate call sites, which a driver cannot cite. The Npc ramified head record is nonempty_npcRamifiedHeadHessian, a Nonempty and not a record value, so that row cannot gain one even if a baseSign theorem were added."

def todoDegreeRoute : String :=
  "TODO: the printed exponent has NO record-field route in any row, because no named baseDim theorem exists anywhere in the tree. Every degree_record_route in every row is therefore null, and the exponent's only binding is the GaussValCell field. Supplying a second route is four small rfl theorems in the three certificate modules, which no exporter lane may add."

def bracket (xs : List String) : String := "[" ++ String.intercalate "," xs ++ "]"

def optString : Option String → String
  | none => "null"
  | some s => jsonString s

def rowJson (row sector cell endpoint normalFormRecord signBridge degreeBridge valueBridge
    displayTheorem valueTheorem : String) (secondSignRoute : Option String)
    (sign : Int) (degree : ℕ) : String :=
  "{\"cell\":" ++ jsonString (GPV ++ cell) ++
  ",\"degree\":" ++ natToString degree ++
  ",\"degree_bridge\":" ++ jsonString (bridgeRoot ++ degreeBridge) ++
  ",\"degree_record_route\":null" ++
  ",\"display_theorem\":" ++ jsonString (GPV ++ displayTheorem) ++
  ",\"endpoint\":" ++ jsonString endpoint ++
  ",\"normal_form_record\":" ++ jsonString normalFormRecord ++
  ",\"record_binding\":" ++ jsonString unboundKind ++
  ",\"row\":" ++ jsonString row ++
  ",\"second_sign_route\":" ++ optString secondSignRoute ++
  ",\"sector\":" ++ jsonString sector ++
  ",\"sign\":" ++ intToString sign ++
  ",\"sign_bridge\":" ++ jsonString (bridgeRoot ++ signBridge) ++
  ",\"value_bridge\":" ++ jsonString (bridgeRoot ++ valueBridge) ++
  ",\"value_theorem\":" ++ jsonString (GPV ++ valueTheorem) ++ "}"

def lRows (h : ℕ) : List String :=
  [ rowJson "graph_normal_form_unramified" "graph_normal_form" "gaussValLUnramCell"
      (LSQ ++ "lSqWallHandlePhase") (LHC ++ "unramifiedHessian")
      "lUnramSign" "lUnramDegree" "lUnramValue"
      "gaussValLUnramifiedDisplay" "gaussValLUnramifiedCell"
      (some (LHC ++ "unramifiedHessian_baseSign")) (-1) (2 * h + 1)
  , rowJson "graph_normal_form_ramified" "graph_normal_form" "gaussValLRamCell"
      (LSQ ++ "lSqWallHandlePhase") (LHC ++ "ramifiedHessian")
      "lRamSign" "lRamDegree" "lRamValue"
      "gaussValLRamifiedDisplay" "gaussValLRamifiedCell"
      (some (LHC ++ "ramifiedHessian_baseSign")) 1 (2 * h + 1) ]

def n0Rows (h : ℕ) : List String :=
  [ rowJson "compact_normal_form" "compact_normal_form" "gaussValCompactCell"
      (WPH ++ "wPhCompactWallHandlePhase") (CNH ++ "compactNUnramifiedHessian")
      "compactSign" "compactDegree" "compactValue"
      "gaussValCompactDisplay" "gaussValCompactCellEq" none 1 (2 * h + 2) ]

def npcRows (h : ℕ) : List String :=
  [ rowJson "unramified_full_offset" "unramified_full_offset" "gaussValCompactCell"
      (WWH ++ "wallHandlePhase") (NHC ++ "npcUnramifiedHeadHessian")
      "compactSign" "compactDegree" "npcValue"
      "gaussValNpcDisplay" "gaussValNpcCellEq" none 1 (2 * h + 2)
  , rowJson "ramified_full_offset" "ramified_full_offset" "gaussValCompactCell"
      (WWH ++ "wallHandlePhase") (NHC ++ "nonempty_npcRamifiedHeadHessian")
      "compactSign" "compactDegree" "npcValue"
      "gaussValNpcDisplay" "gaussValNpcCellEq" none 1 (2 * h + 2) ]

def payload (family : String) (structural : String) (rows : List String) : String :=
  "{\"application_scope\":" ++ jsonString scopeNote ++ "," ++
  "\"cell_note\":" ++ jsonString cellNote ++ "," ++
  "\"cell_structure\":{\"bridge_kind\":" ++ jsonString recordKind ++
    ",\"record\":" ++ jsonString (GPV ++ "GaussValCell") ++
    ",\"value_bridge\":" ++ jsonString (bridgeRoot ++ "cellValue") ++
    ",\"value_def\":" ++ jsonString (GPV ++ "GaussValCell.value") ++ "}," ++
  "\"family\":" ++ jsonString family ++ "," ++
  "\"hash_scope\":" ++ jsonString hashScopeNote ++ "," ++
  "\"rows\":" ++ bracket rows ++ "," ++
  "\"schema\":" ++ jsonString schema ++ "," ++
  "\"sign_binding\":" ++ jsonString recordKind ++ "," ++
  "\"structural\":" ++ structural ++ "," ++
  "\"todos\":" ++ bracket [jsonString todoSecondSignRoute, jsonString todoDegreeRoute] ++ "," ++
  "\"value_binding\":" ++ jsonString restatedKind ++ "," ++
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
      | some h, some q => pure (payload "L" (structuralLN h q) (lRows h))
      | _, _ => throw (IO.userError "L H Q: H and Q must be natural numbers")
    | ["N0", hs, qs] => match hs.toNat?, qs.toNat? with
      | some h, some q => pure (payload "N0" (structuralLN h q) (n0Rows h))
      | _, _ => throw (IO.userError "N0 H Q: H and Q must be natural numbers")
    | ["Npc", hs, qs, rs] => match hs.toNat?, qs.toNat?, rs.toNat? with
      | some h, some q, some r => pure (payload "Npc" (structuralNpc h q r) (npcRows h))
      | _, _, _ => throw (IO.userError "Npc H Q R: H, Q and R must be natural numbers")
    | _ => throw (IO.userError "usage: L H Q | N0 H Q | Npc H Q R")
  IO.println ("W366_LN_GAUSS_JSON=" ++ envelope p)

#print axioms lUnramSign
#print axioms lUnramDegree
#print axioms lRamSign
#print axioms lRamDegree
#print axioms compactSign
#print axioms compactDegree
#print axioms cellValue
#print axioms lUnramValue
#print axioms lRamValue
#print axioms compactValue
#print axioms npcValue
#print axioms exportMain

end GQ2.Dyadic.W366LNGauss

def main (args : List String) : IO Unit := GQ2.Dyadic.W366LNGauss.exportMain args
