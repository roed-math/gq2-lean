/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu
-/
import GQ2.Dyadic.Certificates.LJacobian
import GQ2.Dyadic.Certificates.NpcFox
import GQ2.Dyadic.Word.Export

/-!
# STAGED serializer for the ACTUAL L/N0/Npc evaluated Fox Jacobian (ledger item 3)

This is an exporter driver, not a library module: it carries a global `main` and stays
outside `GQ2.lean`, like the W361 export executables and `scripts/w362_ln_fox_export.lean`.

It serializes ledger item 3, `evaluated Fox Jacobian`, for the same seven L/N0/Npc sectors
that `scripts/w362_ln_fox_export.lean` serializes items 4 and 5 for. Item 3 is the two-row
Jacobian **before** any operation; items 4 and 5 are the operations and the reduced target.

Nothing here retypes a row. The evaluated rows are already concrete Lean data
(`FoxRowNormalForm` values over `FoxCoeff` trees), and for nine of the fourteen rows they are
literally the `target` field of an existing `FoxRowCertificate` with `colOps = []`, i.e. of a
record that certifies the evaluated Fox derivative with no operations applied. Those nine are
bound by `rfl` **signature theorems**. The remaining five rows are the tame row at sectors
where the tree has no such record (the L family at all three, N0 and Npc at the ramified); for those the driver states the denotation theorem itself,
proved from the existing `foxD_tameRelW_*` and `*_toHom_apply` lemmas, exactly as the
existing records prove theirs. Every row therefore carries a named Lean bridge, and the JSON
records which of the two kinds it is: `record_target` or `denotation_theorem`.

The universal-row structure is part of the item. One formal row per family carries an opaque
projector atom `P`, and the branch is a *specialization* of that one row: `P ↦ 1` at the
unramified and scalar sectors, `P ↦ 0` at the ramified sectors. The driver exports the
projector value per sector and binds it by `rfl` to `splitEnd` / `ramifiedEnd`.

Scope. The export instantiates the discrete parameters `h`, `q` and (for Npc) `r`.
Uniformity in those parameters is carried by the quantified signature theorems below, not by
the finite set of exported instances. The export selects no coefficient module, marking,
field, resolver, `eta`, or source certificate, and it is not an approved appendix, manifest
entry, gate or release.
-/

namespace GQ2.Dyadic.W363LNInput

open GQ2 GQ2.FoxH GQ2.Dyadic.Words GQ2.Dyadic.Certificates
open Export (jsonString intToString natToString)

/-! ## Signature theorems, part 1: the wild rows ARE the records' targets

Each is `rfl`. The records certify `foxDHom ⇑t E E₂ w` itself, with `colOps = []`, so their
`target` field is the evaluated wild Fox row and nothing has been applied to it. -/

section LWild
variable {h : ℕ} {C V : Type} [Group C] [Finite C] [AddCommGroup V] [Finite V]
  [DistribMulAction C V] (t : Marking (2*h+1) C) (E : Zhat → ℤ) (E2 : ℤ_[2] → ℤ)
  (hV2 : ∀ v : V, v + v = 0)
  (hwild : ∀ (i : Fin (2*h+1+1)) (v : V), t.x i • v = v)

theorem lSqUnramWild_target (htau : ∀ v : V, t.τ • v = v) :
    (LSq.lSqWildRowCertUnram t E E2 hV2 hwild htau).target = LSq.lSqWildRow h := rfl

theorem lSqUnramWild_colOps (htau : ∀ v : V, t.τ • v = v) :
    (LSq.lSqWildRowCertUnram t E E2 hV2 hwild htau).colOps = [] := rfl

theorem lSqRamWild_target (hfpf : ∀ v : V, t.τ • v = v → v = 0)
    (hodd : ∀ v : V, powOmega2 t.τ • v = v) :
    (LSq.lSqWildRowCertRam t E E2 hV2 hwild hfpf hodd).target = LSq.lSqWildRow h := rfl

theorem lSqRamWild_colOps (hfpf : ∀ v : V, t.τ • v = v → v = 0)
    (hodd : ∀ v : V, powOmega2 t.τ • v = v) :
    (LSq.lSqWildRowCertRam t E E2 hV2 hwild hfpf hodd).colOps = [] := rfl

theorem lSqScalarWild_target (htau : ∀ v : V, t.τ • v = v) (hsigma : ∀ v : V, t.σ • v = v) :
    (LSq.lSqWildRowCertSplit t E E2 hV2 hwild htau hsigma).target
      = FoxRowNormalForm.single .tau := rfl

theorem lSqScalarWild_colOps (htau : ∀ v : V, t.τ • v = v) (hsigma : ∀ v : V, t.σ • v = v) :
    (LSq.lSqWildRowCertSplit t E E2 hV2 hwild htau hsigma).colOps = [] := rfl

end LWild

section N0Wild
variable {h alpha q : ℕ} {C V : Type} [Group C] [Finite C] [AddCommGroup V] [Finite V]
  [DistribMulAction C V] (t : Marking (2 + 2*h) C) (E : Zhat → ℤ) (E2 : ℤ_[2] → ℤ)
  (hV2 : ∀ v : V, v + v = 0)
  (hwild : ∀ (i : Fin (2 + 2*h + 1)) (v : V), t.x i • v = v)

theorem nCompactUnramWild_target (htau : ∀ v : V, t.τ • v = v) (halpha : 1 ≤ alpha) :
    (nCompactWildRowCertUnram (α := alpha) t E E2 hV2 hwild htau halpha).target
      = nCompactWildRow h := rfl

theorem nCompactUnramWild_colOps (htau : ∀ v : V, t.τ • v = v) (halpha : 1 ≤ alpha) :
    (nCompactWildRowCertUnram (α := alpha) t E E2 hV2 hwild htau halpha).colOps = [] := rfl

theorem nCompactRamWild_target (hfpf : ∀ v : V, t.τ • v = v → v = 0)
    (hodd : ∀ v : V, powOmega2 t.τ • v = v) (halpha : 1 ≤ alpha) :
    (nCompactWildRowCertRam (α := alpha) t E E2 hV2 hwild hfpf hodd halpha).target
      = nCompactWildRow h := rfl

theorem nCompactRamWild_colOps (hfpf : ∀ v : V, t.τ • v = v → v = 0)
    (hodd : ∀ v : V, powOmega2 t.τ • v = v) (halpha : 1 ≤ alpha) :
    (nCompactWildRowCertRam (α := alpha) t E E2 hV2 hwild hfpf hodd halpha).colOps = [] := rfl

/-- The N0 tame row at the unramified sector is the `target` of an actual record. -/
theorem nCompactUnramTame_target (htau : ∀ v : V, t.τ • v = v) (hqe : Even q) :
    (tameRowCertUnram (q := q) t E E2 hV2 htau hqe).target = tameUnramRow (2 + 2*h) := rfl

theorem nCompactUnramTame_colOps (htau : ∀ v : V, t.τ • v = v) (hqe : Even q) :
    (tameRowCertUnram (q := q) t E E2 hV2 htau hqe).colOps = [] := rfl

end N0Wild

section NpcWild
variable {h alpha r q : ℕ} {C V : Type} [Group C] [Finite C] [AddCommGroup V] [Finite V]
  [DistribMulAction C V] (t : Marking (2 + 2*h) C) (E : Zhat → ℤ) (E2 : ℤ_[2] → ℤ)
  (hV2 : ∀ v : V, v + v = 0)
  (hwild : ∀ (i : Fin (2 + 2*h + 1)) (v : V), t.x i • v = v)

theorem npcUnramWild_target (htau : ∀ v : V, t.τ • v = v) (halpha : 1 ≤ alpha) (e : EtaData) :
    (Npc.npcWildRowCertUnram (α := alpha) (r := r) t E E2 hV2 hwild htau halpha e).target
      = Npc.npcWildRow h r := rfl

theorem npcUnramWild_colOps (htau : ∀ v : V, t.τ • v = v) (halpha : 1 ≤ alpha) (e : EtaData) :
    (Npc.npcWildRowCertUnram (α := alpha) (r := r) t E E2 hV2 hwild htau halpha e).colOps
      = [] := rfl

theorem npcRamWild_target (hfpf : ∀ v : V, t.τ • v = v → v = 0)
    (hodd : ∀ v : V, powOmega2 t.τ • v = v) (halpha : 1 ≤ alpha) (e : EtaData) :
    (Npc.npcWildRowCertRam (α := alpha) (r := r) t E E2 hV2 hwild hfpf hodd halpha e).target
      = Npc.npcWildRow h r := rfl

theorem npcRamWild_colOps (hfpf : ∀ v : V, t.τ • v = v → v = 0)
    (hodd : ∀ v : V, powOmega2 t.τ • v = v) (halpha : 1 ≤ alpha) (e : EtaData) :
    (Npc.npcWildRowCertRam (α := alpha) (r := r) t E E2 hV2 hwild hfpf hodd halpha e).colOps
      = [] := rfl

/-- The Npc tame row at the unramified sector is the `target` of an actual record. -/
theorem npcUnramTame_target (htau : ∀ v : V, t.τ • v = v) (hqe : Even q) (e : EtaData) :
    (Npc.npcTameRowCertUnram (q := q) t E E2 hV2 htau hqe e).target
      = Npc.tameUnramRow (2 + 2*h) := rfl

theorem npcUnramTame_colOps (htau : ∀ v : V, t.τ • v = v) (hqe : Even q) (e : EtaData) :
    (Npc.npcTameRowCertUnram (q := q) t E E2 hV2 htau hqe e).colOps = [] := rfl

end NpcWild

/-! ## Signature theorems, part 2: the tame rows with no record of their own

The tree has a tame-row `FoxRowCertificate` only at the unramified sectors of N0 and Npc. The
L family has none at any sector, and no family has one at the ramified sector, where the tame
row is `tameRow n q` and enters through `foxD_tameRelW_of_tameRel` inside the two-row
`verifies`. The four theorems below state exactly the denotations those `verifies` blocks
use, at general `n`, so that every exported tame row has a named bridge. They are the
driver's own declarations, not references to existing ones, and the JSON marks them
`denotation_theorem` rather than `record_target`. -/

section TameInput
variable {n q : ℕ} {C V : Type} [Group C] [Finite C] [AddCommGroup V] [Finite V]
  [DistribMulAction C V] (t : Marking n C) (E : Zhat → ℤ) (E2 : ℤ_[2] → ℤ)

/-- The evaluated tame row at a split or unramified module IS `tameUnramRow n` read with
`P ↦ 1`. This is the identity `tameRowCertUnram.verifies` proves at `n = 2 + 2h`. -/
theorem tameUnramInput_denote (hV2 : ∀ v : V, v + v = 0) (htau : ∀ v : V, t.τ • v = v)
    (hqe : Even q) (a : Generator n → V) :
    foxD ⇑t a E E2 (tameRelW n q) = (tameUnramRow n).toHom (TameSym.splitEnd t) a := by
  rw [foxD_tameRelW_unram t E E2 hV2 htau hqe, TameSym.splitEnd, tameUnramRow_toHom_apply]

/-- The evaluated tame row at a ramified module IS `tameRow n q` read with `P ↦ 0`, under the
actual tame relation. This is the identity the ramified two-row `verifies` blocks use. -/
theorem tameRamInput_denote (hrel : conjR t.τ t.σ = t.τ ^ q) (a : Generator n → V) :
    foxD ⇑t a E E2 (tameRelW n q) = (tameRow n q).toHom (TameSym.ramifiedEnd t) a := by
  rw [foxD_tameRelW_of_tameRel t E E2 hrel, TameSym.ramifiedEnd, tameRow_toHom_apply]
  simp only [smul_add, smul_sub]
  abel

/-- The Npc twin of `tameUnramInput_denote`, over the η̂-alphabet. -/
theorem npcTameUnramInput_denote (A : C) (hV2 : ∀ v : V, v + v = 0)
    (htau : ∀ v : V, t.τ • v = v) (hqe : Even q) (a : Generator n → V) :
    foxD ⇑t a E E2 (Npc.tameRelW n q)
      = (Npc.tameUnramRow n).toHom (Npc.NpcSym.splitEnd t A) a := by
  rw [Npc.foxD_tameRelW_unram t E E2 hV2 htau hqe, Npc.NpcSym.splitEnd,
    Npc.tameUnramRow_toHom_apply]

/-- The Npc twin of `tameRamInput_denote`, over the η̂-alphabet. -/
theorem npcTameRamInput_denote (A : C) (hrel : conjR t.τ t.σ = t.τ ^ q)
    (a : Generator n → V) :
    foxD ⇑t a E E2 (Npc.tameRelW n q)
      = (Npc.tameRow n q).toHom (Npc.NpcSym.ramifiedEnd t A) a := by
  rw [Npc.foxD_tameRelW_of_tameRel t E E2 hrel, Npc.NpcSym.ramifiedEnd, Npc.tameRow_toHom_apply]
  simp only [smul_add, smul_sub]
  abel

end TameInput

/-! ## Signature theorems, part 3: the projector specialization

The branch is a specialization of one universal row, not a second row. -/

section Projector
variable {n : ℕ} {C V : Type} [Group C] [AddCommGroup V] [DistribMulAction C V]
  (t : Marking n C)

theorem tameSplit_projector : TameSym.splitEnd (A := V) t = TameSym.toEnd t 1 := rfl

theorem tameRamified_projector : TameSym.ramifiedEnd (A := V) t = TameSym.toEnd t 0 := rfl

theorem npcSplit_projector (A : C) :
    Npc.NpcSym.splitEnd (V := V) t A = Npc.NpcSym.toEnd t A 1 := rfl

theorem npcRamified_projector (A : C) :
    Npc.NpcSym.ramifiedEnd (V := V) t A = Npc.NpcSym.toEnd t A 0 := rfl

end Projector

/-! ## Canonical JSON serialization

Keys are emitted in ASCII order so that the bytes agree with Python's
`json.dumps(..., sort_keys=True, separators=(",",":"))` used by the checker. -/

def generatorJson {n : ℕ} : Generator n → String
  | .sigma => "{\"kind\":\"sigma\"}"
  | .tau => "{\"kind\":\"tau\"}"
  | .wild i => "{\"index\":" ++ natToString i.val ++ ",\"kind\":\"wild\"}"

def tameSymJson {n : ℕ} : TameSym n → String
  | .gen g z => "{\"generator\":" ++ generatorJson g ++
      ",\"kind\":\"generator_power\",\"power\":" ++ intToString z ++ "}"
  | .sigma2 z => "{\"kind\":\"sigma2_power\",\"power\":" ++ intToString z ++ "}"
  | .proj => "{\"kind\":\"projector\"}"

def npcSymJson {n : ℕ} : Npc.NpcSym n → String
  | .std s => "{\"kind\":\"standard\",\"symbol\":" ++ tameSymJson s ++ "}"
  | .etaA k => "{\"kind\":\"eta_conjugator_power\",\"power\":" ++ intToString k ++ "}"

/-- Coefficient trees over an arbitrary atom alphabet, given that alphabet's serializer.
`comp p q` denotes the product `eval p * eval q` in `AddMonoid.End`, so `p` is the outer
operator and `q` the inner one. -/
def coeffJson {S : Type} (atom : S → String) : FoxCoeff S → String
  | .zero => "{\"op\":\"zero\"}"
  | .one => "{\"op\":\"one\"}"
  | .atom s => "{\"op\":\"atom\",\"symbol\":" ++ atom s ++ "}"
  | .add p q => "{\"left\":" ++ coeffJson atom p ++ ",\"op\":\"add\",\"right\":" ++
      coeffJson atom q ++ "}"
  | .comp p q => "{\"inner\":" ++ coeffJson atom q ++ ",\"op\":\"comp\",\"outer\":" ++
      coeffJson atom p ++ "}"
  | .neg p => "{\"op\":\"neg\",\"value\":" ++ coeffJson atom p ++ "}"

def colOpJson {n : ℕ} {S : Type} (atom : S → String) : FoxColOp (Generator n) S → String
  | .swap g g' => "{\"left\":" ++ generatorJson g ++ ",\"op\":\"swap\",\"right\":" ++
      generatorJson g' ++ "}"
  | .transvect g g' c => "{\"coefficient\":" ++ coeffJson atom c ++
      ",\"op\":\"transvect\",\"source\":" ++ generatorJson g' ++ ",\"target\":" ++
      generatorJson g ++ "}"
  | .scale g c d => "{\"forward\":" ++ coeffJson atom c ++ ",\"generator\":" ++
      generatorJson g ++ ",\"inverse\":" ++ coeffJson atom d ++ ",\"op\":\"scale\"}"

/-- Every column slot of the alphabet, in the fixed order sigma, tau, x0, ..., xn. -/
def columns (n : ℕ) : List (Generator n) :=
  Generator.sigma :: Generator.tau :: (List.finRange (n+1)).map Generator.wild

def bracket (xs : List String) : String := "[" ++ String.intercalate "," xs ++ "]"

def rowJson {n : ℕ} {S : Type} (atom : S → String)
    (row : FoxRowNormalForm (Generator n) S) : String :=
  "{\"columns\":" ++ bracket ((columns n).map (fun g =>
    "{\"coefficient\":" ++ coeffJson atom (row.row g) ++ ",\"generator\":" ++
      generatorJson g ++ "}")) ++ "}"

/-- A serialized evaluated row: the formal data, the Lean declaration that binds it, and which
of the two kinds of binding that declaration is. -/
def inputRowJson {n : ℕ} {S : Type} (atom : S → String) (bridge kind : String)
    (row : FoxRowNormalForm (Generator n) S) : String :=
  "{\"bridge\":" ++ jsonString bridge ++ ",\"bridge_kind\":" ++ jsonString kind ++
  ",\"row\":" ++ rowJson atom row ++ "}"

def recordKind : String := "record_target"
def theoremKind : String := "denotation_theorem"

/-- The record's `colOps` field, serialized. Item 3 is the Jacobian before any operation, so
every sector's list is empty; the `*_colOps` signature theorems are what say so. -/
def colOpsJson {n : ℕ} {S : Type} (atom : S → String)
    (ops : List (FoxColOp (Generator n) S)) : String :=
  bracket (ops.map (colOpJson atom))

def sectorJson (name record alphabet projector projectorBridge colOps : String)
    (tameRowJson wildRowJson : String) : String :=
  "{\"column_operations\":" ++ colOps ++
  ",\"projector\":" ++ jsonString projector ++
  ",\"projector_bridge\":" ++ jsonString projectorBridge ++
  ",\"record\":" ++ jsonString record ++
  ",\"sector\":" ++ jsonString name ++
  ",\"symbol_alphabet\":" ++ jsonString alphabet ++
  ",\"tame_row\":" ++ tameRowJson ++
  ",\"wild_row\":" ++ wildRowJson ++ "}"

def schema : String := "gq2.w363.ln-input-rows.v1.staged"
def hashDomain : String := "GQ2-W363-LN-INPUT-ROWS\x00"
def certRoot : String := "GQ2.Dyadic.Certificates."
def bridgeRoot : String := "GQ2.Dyadic.W363LNInput."

def scopeNote : String :=
  "Ledger item 3 only, for the existing L/N0/Npc evaluated Fox rows under their own stated hypotheses. No coefficient module, marking, field, resolver, eta or source certificate is selected."

def interpretationNote : String :=
  "One universal wild row per family carries the opaque projector atom P. The branch is a specialization of that row: P maps to the identity at the unramified and scalar sectors and to zero at the ramified sectors. The exported projector value is bound by rfl to splitEnd or ramifiedEnd."

def hashScopeNote : String :=
  "Identity of the serialized evaluated rows at the stated discrete parameters. Uniformity in h, q and r is carried by the signature theorems, not by this instance."

/-! ### The seven sectors -/

/-- The three families' empty column-operation lists, at their own alphabets. -/
def lNoColOps (h : ℕ) : String :=
  colOpsJson tameSymJson ([] : List (FoxColOp (Generator (2*h+1)) (TameSym (2*h+1))))

def n0NoColOps (h : ℕ) : String :=
  colOpsJson tameSymJson ([] : List (FoxColOp (Generator (2+2*h)) (TameSym (2+2*h))))

def npcNoColOps (h : ℕ) : String :=
  colOpsJson npcSymJson ([] : List (FoxColOp (Generator (2+2*h)) (Npc.NpcSym (2+2*h))))

def lTameUnram (h : ℕ) : String :=
  inputRowJson tameSymJson (bridgeRoot ++ "tameUnramInput_denote") theoremKind
    (tameUnramRow (2*h+1))

def lSectors (h q : ℕ) : List String :=
  [ sectorJson "unramified" (certRoot ++ "LSq.lSqWildRowCertUnram") "TameSym"
      "one" (bridgeRoot ++ "tameSplit_projector") (lNoColOps h)
      (lTameUnram h)
      (inputRowJson tameSymJson (bridgeRoot ++ "lSqUnramWild_target") recordKind
        (LSq.lSqWildRow h))
  , sectorJson "ramified" (certRoot ++ "LSq.lSqWildRowCertRam") "TameSym"
      "zero" (bridgeRoot ++ "tameRamified_projector") (lNoColOps h)
      (inputRowJson tameSymJson (bridgeRoot ++ "tameRamInput_denote") theoremKind
        (tameRow (2*h+1) q))
      (inputRowJson tameSymJson (bridgeRoot ++ "lSqRamWild_target") recordKind
        (LSq.lSqWildRow h))
  , sectorJson "scalar" (certRoot ++ "LSq.lSqWildRowCertSplit") "TameSym"
      "one" (bridgeRoot ++ "tameSplit_projector") (lNoColOps h)
      (lTameUnram h)
      (inputRowJson tameSymJson (bridgeRoot ++ "lSqScalarWild_target") recordKind
        (FoxRowNormalForm.single (S := TameSym (2*h+1)) (Generator.tau (n := 2*h+1)))) ]

def n0Sectors (h q : ℕ) : List String :=
  [ sectorJson "unramified" (certRoot ++ "nCompactWildRowCertUnram") "TameSym"
      "one" (bridgeRoot ++ "tameSplit_projector") (n0NoColOps h)
      (inputRowJson tameSymJson (bridgeRoot ++ "nCompactUnramTame_target") recordKind
        (tameUnramRow (2 + 2*h)))
      (inputRowJson tameSymJson (bridgeRoot ++ "nCompactUnramWild_target") recordKind
        (nCompactWildRow h))
  , sectorJson "ramified" (certRoot ++ "nCompactWildRowCertRam") "TameSym"
      "zero" (bridgeRoot ++ "tameRamified_projector") (n0NoColOps h)
      (inputRowJson tameSymJson (bridgeRoot ++ "tameRamInput_denote") theoremKind
        (tameRow (2 + 2*h) q))
      (inputRowJson tameSymJson (bridgeRoot ++ "nCompactRamWild_target") recordKind
        (nCompactWildRow h)) ]

def npcSectors (h r q : ℕ) : List String :=
  [ sectorJson "unramified" (certRoot ++ "Npc.npcWildRowCertUnram") "NpcSym"
      "one" (bridgeRoot ++ "npcSplit_projector") (npcNoColOps h)
      (inputRowJson npcSymJson (bridgeRoot ++ "npcUnramTame_target") recordKind
        (Npc.tameUnramRow (2 + 2*h)))
      (inputRowJson npcSymJson (bridgeRoot ++ "npcUnramWild_target") recordKind
        (Npc.npcWildRow h r))
  , sectorJson "ramified" (certRoot ++ "Npc.npcWildRowCertRam") "NpcSym"
      "zero" (bridgeRoot ++ "npcRamified_projector") (npcNoColOps h)
      (inputRowJson npcSymJson (bridgeRoot ++ "npcTameRamInput_denote") theoremKind
        (Npc.tameRow (2 + 2*h) q))
      (inputRowJson npcSymJson (bridgeRoot ++ "npcRamWild_target") recordKind
        (Npc.npcWildRow h r)) ]

def payload (family : String) (n h : ℕ) (structural : String)
    (sectors : List String) : String :=
  "{\"alphabet\":{\"degree\":" ++ natToString n ++ ",\"h\":" ++ natToString h ++
    ",\"wild_count\":" ++ natToString (n+1) ++ "}," ++
  "\"application_scope\":" ++ jsonString scopeNote ++ "," ++
  "\"family\":" ++ jsonString family ++ "," ++
  "\"hash_scope\":" ++ jsonString hashScopeNote ++ "," ++
  "\"interpretation\":" ++ jsonString interpretationNote ++ "," ++
  "\"schema\":" ++ jsonString schema ++ "," ++
  "\"sectors\":" ++ bracket sectors ++ "," ++
  "\"structural\":" ++ structural ++ "}"

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
      | some h, some q => pure (payload "L" (2*h+1) h (structuralLN h q) (lSectors h q))
      | _, _ => throw (IO.userError "L H Q: H and Q must be natural numbers")
    | ["N0", hs, qs] => match hs.toNat?, qs.toNat? with
      | some h, some q => pure (payload "N0" (2+2*h) h (structuralLN h q) (n0Sectors h q))
      | _, _ => throw (IO.userError "N0 H Q: H and Q must be natural numbers")
    | ["Npc", hs, qs, rs] => match hs.toNat?, qs.toNat?, rs.toNat? with
      | some h, some q, some r =>
          pure (payload "Npc" (2+2*h) h (structuralNpc h q r) (npcSectors h r q))
      | _, _, _ => throw (IO.userError "Npc H Q R: H, Q and R must be natural numbers")
    | _ => throw (IO.userError "usage: L H Q | N0 H Q | Npc H Q R")
  IO.println ("W363_LN_INPUT_JSON=" ++ envelope p)

#print axioms lSqUnramWild_target
#print axioms lSqUnramWild_colOps
#print axioms lSqRamWild_target
#print axioms lSqRamWild_colOps
#print axioms lSqScalarWild_target
#print axioms lSqScalarWild_colOps
#print axioms nCompactUnramWild_target
#print axioms nCompactUnramWild_colOps
#print axioms nCompactRamWild_target
#print axioms nCompactRamWild_colOps
#print axioms nCompactUnramTame_target
#print axioms nCompactUnramTame_colOps
#print axioms npcUnramWild_target
#print axioms npcUnramWild_colOps
#print axioms npcRamWild_target
#print axioms npcRamWild_colOps
#print axioms npcUnramTame_target
#print axioms npcUnramTame_colOps
#print axioms tameUnramInput_denote
#print axioms tameRamInput_denote
#print axioms npcTameUnramInput_denote
#print axioms npcTameRamInput_denote
#print axioms tameSplit_projector
#print axioms tameRamified_projector
#print axioms npcSplit_projector
#print axioms npcRamified_projector
#print axioms exportMain

end GQ2.Dyadic.W363LNInput

def main (args : List String) : IO Unit := GQ2.Dyadic.W363LNInput.exportMain args
