/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu
-/
import GQ2.Dyadic.Certificates.L
import GQ2.Dyadic.Certificates.N0
import GQ2.Dyadic.Instances.NpcUnramifiedFullOffsetHessian
import GQ2.Dyadic.Instances.NpcRamifiedFullOffsetHessian
import GQ2.Dyadic.Word.Export

/-!
# STAGED serializer for the L/N0/Npc extraspecial Hessian (ledger item 7)

This is an exporter driver, not a library module: it carries a global `main` and stays
outside `GQ2.lean`, like the other W361/W362/W363 export executables.

**A third kind of bridge.** Item 7's carriers are *theorems*, not records with data fields,
so neither of the two earlier kinds applies. Items 3, 4 and 5 bind a serialized value to the
record field it came from by `rfl` (`record_target`). Item 6 has no data at all and binds a
`Prop`-valued field by statement identity (`field_statement_identity`). Item 7 sits between
them: the identity has real algebraic shape, but that shape lives in a theorem statement.

So the driver **restates each identity through a named decomposition and discharges the
restatement by the tree's own theorem**:

```
hessShape leading cross planes = leading + cross + ∑ j, planes j
```

`lHessian_shape`, `n0Hessian_shape`, `npcUnramHessian_shape` and `npcRamHessian_shape` each
say that the actual `hessRelZ` value of the actual word **is** `hessShape` applied to three
specific subterms, and each is proved by applying the existing theorem. A wrong
decomposition does not compile. What is therefore certified is the *decomposition*: that the
Hessian is a leading term plus one cross term plus a sum over the `h` handle planes, with
those three pieces. The JSON's human labels for the three pieces are prose, exactly like
item 6's clause roles, and the artifact says so.

**What the four identities do not share.** The hypotheses differ, and that is the content
worth publishing:

* L and N0 are **resolver-immune** and read an `x`-slot-zero slice: L hypothesises
  `v x0 = 0`, N0 hypothesises `v x2 = 0` and `2 <= alpha`, and neither needs any pin on
  `E omega2`.
* The two Npc identities are the **full-offset** route, with no vanishing slot, and each
  needs its own extra input: the unramified one needs a residue pin `E omega2 = e` with
  `e % 4 = 1`, and the ramified one needs quadraticity of `q`, an odd-order fixed-point-free
  `u`, and a resolver-lifting hypothesis.

The full-offset route is deliberate: it is the completed Npc proof, and the older Gate-E
slice with an invertible `Lc` is not what these bridges name.

Scope. No coefficient module, marking, field, resolver, `eta` or source certificate is
selected: every theorem below is quantified over all of them. This is not an approved
appendix, manifest entry, gate or release.
-/

namespace GQ2.Dyadic.W363LNHessian

open GQ2 GQ2.QuadraticFp2 GQ2.SectionSix
open GQ2.Dyadic.Words GQ2.Dyadic.Certificates
open GQ2.Dyadic.Export (jsonString natToString)

/-- The common shape of the four item-7 identities: a leading term, one cross term, and a
sum over the `h` handle planes. This is the decomposition the signature theorems certify. -/
def hessShape {h : ℕ} (leading cross : ZMod 2) (planes : Fin h → ZMod 2) : ZMod 2 :=
  leading + cross + ∑ j, planes j

section Shapes
variable {C V : Type} [Group C] [AddCommGroup V] [DistribMulAction C V]
  {q : V → ZMod 2} (dat : FactorSet C V) (hdat : IsEquivariantFactorSet q dat)

/-- **L.** Leading term the quadratic value at `x1`; cross term the Wall doubling of that
slot by the `omega2`-operator; then the handle planes. Slot `x0` is hypothesised zero, and
no pin on `E omega2` is needed. -/
theorem lHessian_shape {h : ℕ} (hV2 : ∀ v : V, v + v = 0) (s u : C)
    (v : Fin (2 * h + 1 + 1) → V) (hv0 : v (LSqStokes.lSqIdx0 h) = 0)
    (E : Zhat → ℤ) (E2 : ℤ_[2] → ℤ) :
    hessRelZ (LSqStokes.lSqHessMark s u v) (kappa0Cocycle dat hdat) E E2
        (Words.LSq.lSqW h)
      = hessShape (q (v (LSqStokes.lSqIdx1 h)))
          (polar q (v (LSqStokes.lSqIdx1 h)) ((s ^ E omega2)⁻¹ • v (LSqStokes.lSqIdx1 h)))
          (fun j => polar q (v (LSqStokes.lSqIdxU j)) (v (LSqStokes.lSqIdxV j))) :=
  LSqStokes.hessRelZ_lSq dat hdat hV2 s u v hv0 E E2

/-- **N0.** Leading term the quadratic value at `x0`; cross term the polar pairing of `x0`
against `x1`; then the handle planes. Slot `x2` is hypothesised zero, `2 <= alpha` enters
once through the leading-power law, and no pin on `E omega2` is needed. -/
theorem n0Hessian_shape {h alpha : ℕ} (hV2 : ∀ v : V, v + v = 0) (halpha : 2 ≤ alpha) (s u : C)
    (v : Fin (2 + 2 * h + 1) → V) (hv2 : v (x2Idx h) = 0)
    (E : Zhat → ℤ) (E2 : ℤ_[2] → ℤ) :
    hessRelZ (hessMark s u v) (kappa0Cocycle dat hdat) E E2 (nCompactW alpha h)
      = hessShape (q (v (x0Idx h))) (polar q (v (x0Idx h)) (v (x1Idx h)))
          (fun j => polar q (v (hIdxU j)) (v (hIdxV j))) :=
  hessRelZ_nCompact dat hdat hV2 halpha s u v hv2 E E2

end Shapes

section NpcUnramShape
variable {C V : Type} [Group C] [AddCommGroup V] [DistribMulAction C V]
  {q : V → ZMod 2} (dat : FactorSet C V) (hdat : IsEquivariantFactorSet q dat)
  [Finite C] [Finite V] [TopologicalSpace C] [DiscreteTopology C]

/-- **Npc, unramified full offset.** Leading term the named unramified diagonal, not a bare
quadratic value; cross term the polar pairing of `c1` against `Phi c0`; then the handle
planes. There is **no vanishing slot**, and the identity needs the residue pin
`E omega2 = e` with `e % 4 = 1`. -/
theorem npcUnramHessian_shape {h : ℕ} (s : C) (E : Zhat → ℤ) (E2 : ℤ_[2] → ℤ)
    (hV2 : ∀ v : V, v + v = 0) {eomega : ℕ} (hE : E omega2 = (eomega : ℤ))
    (he : eomega % 4 = 1) (alpha r : ℕ) (d : EtaData) (Phi : V →+ V) (c0 c1 : V)
    (z : Fin h × Fin 2 → V) :
    hessRelZ (hessMark s 1 (Instances.NpcUnramifiedFullOffsetHessian.npcPhiOffsets h Phi c0 c1 z))
        (kappa0Cocycle dat hdat) E E2 (Words.Npc.npcW alpha r h d)
      = hessShape
          (Instances.NpcUnramifiedFullOffsetHessian.npcUnramifiedDiagonal dat hdat s E alpha r
            d Phi c0)
          (polar q c1 (Phi c0))
          (fun j => polar q (z (j, 0)) (z (j, 1))) :=
  Instances.NpcUnramifiedFullOffsetHessian.hessRelZ_npcW_evenPhiNormal dat hdat s E E2 hV2 hE
    he alpha r d Phi c0 c1 z

end NpcUnramShape

section NpcRamShape
variable {C V : Type} [Group C] [AddCommGroup V] [DistribMulAction C V]
  {q : V → ZMod 2} (dat : FactorSet C V) (hdat : IsEquivariantFactorSet q dat)
  [Finite C] [Finite V]

/-- **Npc, ramified full offset.** Leading term the named ramified diagonal; cross term the
polar pairing of `c1` against the `eta`-twisted image of `c0`; then the handle planes. There
is **no vanishing slot**, and the identity needs quadraticity of `q`, an odd-order
fixed-point-free `u`, and a resolver-lifting hypothesis. -/
theorem npcRamHessian_shape (hq : IsQuadraticFp2 q) (hV2 : ∀ v : V, v + v = 0)
    (h : ℕ) (s u : C) (hu : Odd (orderOf u)) (hVu : ∀ v : V, u • v = v → v = 0)
    (E : Zhat → ℤ) (E2 : ℤ_[2] → ℤ) (alpha r : ℕ) (d : EtaData) (c0 c1 : V)
    (z : Fin h × Fin 2 → V)
    (hres : MProcyclic.ResolverLifts E (WordCoh.CentExt (kappa0Cocycle dat hdat))) :
    hessRelZ
        (hessMark s u (Instances.NpcRamifiedFullOffsetHessian.npcTwistedOffsets h
          (s ^ E d.toZhat)⁻¹ (s ^ ((2 : ℤ) ^ r))⁻¹ c0 c1 z))
        (kappa0Cocycle dat hdat) E E2 (Words.Npc.npcW alpha r h d)
      = hessShape
          (Instances.NpcRamifiedFullOffsetHessian.npcRamifiedDiagonal dat hdat s u E alpha r
            d c0)
          (polar q c1 ((s ^ E d.toZhat)⁻¹ • c0))
          (fun j => polar q (z (j, 0)) (z (j, 1))) :=
  Instances.NpcRamifiedFullOffsetHessian.hessRelZ_npcW_evenTwistedNormal dat hdat hq hV2 h s u
    hu hVu E E2 alpha r d c0 c1 z hres

end NpcRamShape

/-! ## Canonical JSON serialization

Keys are emitted in ASCII order so that the bytes agree with Python's
`json.dumps(..., sort_keys=True, separators=(",",":"))` used by the checker. -/

def schema : String := "gq2.w363.ln-hessian.v1.staged"
def hashDomain : String := "GQ2-W363-LN-HESSIAN\x00"
def bridgeRoot : String := "GQ2.Dyadic.W363LNHessian."
def restatedKind : String := "restated_identity"

def scopeNote : String :=
  "Ledger item 7 only: the decomposition of the L/N0/Npc word-side Hessian identity into a leading term, one cross term and the handle planes, together with the hypotheses each sector actually needs. No coefficient module, marking, field, resolver, eta or source certificate is selected: every signature theorem is quantified over all of them."

def warningNote : String :=
  "Item 7's carriers are theorems, not records with data fields, so no value is bound by rfl here. The driver restates each identity through the named decomposition hessShape and discharges the restatement by the tree's own theorem, so a wrong decomposition does not compile. What is certified is the decomposition and its three subterms. The human labels below are prose, not Lean, exactly like the item 6 clause roles."

def hashScopeNote : String :=
  "Identity of the serialized decomposition, hypothesis list and handle-plane count at the stated discrete parameters. It is not a hash of any proof."

def shapeNote : String :=
  "hessShape leading cross planes = leading + cross + sum over j of planes j, with j ranging over the h handle planes."

/-- One hypothesis the sector's identity actually binds, with the role it plays. -/
def hypothesisJson (id role : String) : String :=
  "{\"id\":" ++ jsonString id ++ ",\"role\":" ++ jsonString role ++ "}"

def bracket (xs : List String) : String := "[" ++ String.intercalate "," xs ++ "]"

/-- One sector: the decomposition's three pieces, the two Lean declarations that bind it,
the hypotheses, and whether a slot is hypothesised zero. -/
def sectorJson (name bridge source leading leadingKind cross : String)
    (hypotheses : List String) (vanishing : String) : String :=
  "{\"bridge\":" ++ jsonString bridge ++
  ",\"bridge_kind\":" ++ jsonString restatedKind ++
  ",\"cross\":" ++ jsonString cross ++
  ",\"hypotheses\":" ++ bracket hypotheses ++
  ",\"leading\":" ++ jsonString leading ++
  ",\"leading_kind\":" ++ jsonString leadingKind ++
  ",\"sector\":" ++ jsonString name ++
  ",\"source\":" ++ jsonString source ++
  ",\"vanishing_slot\":" ++ vanishing ++ "}"

def stokesRoot : String := "GQ2.Dyadic.Certificates."
def npcUnramRoot : String := "GQ2.Dyadic.Instances.NpcUnramifiedFullOffsetHessian."
def npcRamRoot : String := "GQ2.Dyadic.Instances.NpcRamifiedFullOffsetHessian."

def lSectors : List String :=
  [ sectorJson "slice" (bridgeRoot ++ "lHessian_shape")
      (stokesRoot ++ "LSqStokes.hessRelZ_lSq")
      "the quadratic value q at the x1 slot" "quadratic_slot"
      "the Wall doubling of the x1 slot by the omega2-operator: polar q at x1 against the inverse omega2-power acting on x1"
      [ hypothesisJson "char_two" "every module element is its own negative"
      , hypothesisJson "x0_slot_zero" "the x0 slot of the offset vector is zero" ]
      (jsonString "x0") ]

def n0Sectors : List String :=
  [ sectorJson "slice" (bridgeRoot ++ "n0Hessian_shape")
      (stokesRoot ++ "hessRelZ_nCompact")
      "the quadratic value q at the x0 slot" "quadratic_slot"
      "the polar pairing of the x0 slot against the x1 slot"
      [ hypothesisJson "char_two" "every module element is its own negative"
      , hypothesisJson "alpha_at_least_two" "enters exactly once, through the leading-power law"
      , hypothesisJson "x2_slot_zero" "the x2 slot of the offset vector is zero" ]
      (jsonString "x2") ]

def npcSectors : List String :=
  [ sectorJson "unramified_full_offset" (bridgeRoot ++ "npcUnramHessian_shape")
      (npcUnramRoot ++ "hessRelZ_npcW_evenPhiNormal")
      "the named unramified diagonal npcUnramifiedDiagonal, not a bare quadratic value"
      "named_diagonal"
      "the polar pairing of c1 against the image of c0 under the normal-form operator Phi"
      [ hypothesisJson "char_two" "every module element is its own negative"
      , hypothesisJson "omega2_residue_pin" "E omega2 is a natural number congruent to 1 mod 4"
      , hypothesisJson "finite_discrete_marking" "the marking group is finite and discrete" ]
      "null"
  , sectorJson "ramified_full_offset" (bridgeRoot ++ "npcRamHessian_shape")
      (npcRamRoot ++ "hessRelZ_npcW_evenTwistedNormal")
      "the named ramified diagonal npcRamifiedDiagonal, not a bare quadratic value"
      "named_diagonal"
      "the polar pairing of c1 against the eta-twisted image of c0"
      [ hypothesisJson "char_two" "every module element is its own negative"
      , hypothesisJson "quadratic_form" "q is a quadratic form over F2, not merely a function"
      , hypothesisJson "odd_fixed_point_free_u" "the tame marking u has odd order and no nonzero fixed vector"
      , hypothesisJson "resolver_lifts" "the resolver lifts to the central extension" ]
      "null" ]

def payload (family : String) (n h : ℕ) (structural : String)
    (sectors : List String) : String :=
  "{\"application_scope\":" ++ jsonString scopeNote ++ "," ++
  "\"decomposition\":{\"bridge\":" ++ jsonString (bridgeRoot ++ "hessShape") ++
    ",\"note\":" ++ jsonString shapeNote ++ ",\"planes\":" ++ natToString h ++ "}," ++
  "\"degree\":" ++ natToString n ++ "," ++
  "\"family\":" ++ jsonString family ++ "," ++
  "\"hash_scope\":" ++ jsonString hashScopeNote ++ "," ++
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
      | some h, some q => pure (payload "L" (2*h+1) h (structuralLN h q) lSectors)
      | _, _ => throw (IO.userError "L H Q: H and Q must be natural numbers")
    | ["N0", hs, qs] => match hs.toNat?, qs.toNat? with
      | some h, some q => pure (payload "N0" (2+2*h) h (structuralLN h q) n0Sectors)
      | _, _ => throw (IO.userError "N0 H Q: H and Q must be natural numbers")
    | ["Npc", hs, qs, rs] => match hs.toNat?, qs.toNat?, rs.toNat? with
      | some h, some q, some r =>
          pure (payload "Npc" (2+2*h) h (structuralNpc h q r) npcSectors)
      | _, _, _ => throw (IO.userError "Npc H Q R: H, Q and R must be natural numbers")
    | _ => throw (IO.userError "usage: L H Q | N0 H Q | Npc H Q R")
  IO.println ("W363_LN_HESSIAN_JSON=" ++ envelope p)

#print axioms hessShape
#print axioms lHessian_shape
#print axioms n0Hessian_shape
#print axioms npcUnramHessian_shape
#print axioms npcRamHessian_shape
#print axioms exportMain

end GQ2.Dyadic.W363LNHessian

def main (args : List String) : IO Unit := GQ2.Dyadic.W363LNHessian.exportMain args
