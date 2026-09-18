/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu
-/
import GQ2.Dyadic.Certificates.LJacobian
import GQ2.Dyadic.Certificates.NpcFox
import GQ2.Dyadic.Word.Export

/-!
# STAGED serializer for the ACTUAL L/N0/Npc Fox operation lists and normal matrices

This is an exporter driver, not a library module: it carries a global `main` and stays
outside `GQ2.lean`, like the other W361 export executables.

It serializes ledger items 4 and 5 (`invertible row/column operations` and
`reduced normal matrix`) for the seven existing L/N0/Npc `FoxCertificate` sectors.
Nothing here retypes a matrix from prose. Every exported list and target is the value of an
existing definition, and each sector carries `rfl` **signature theorems** proving that the
serialized value is definitionally the corresponding field of the actual record
(`lSqJacobianCertUnram`, `nCompactJacobianCertRam`, ...). The three sector values that the
records spell inline are given names here and bound by the same `rfl` theorems.

Scope. The export instantiates the discrete parameters `h`, `q` and (for Npc) `r`, because
`tameRow _ q` really contains `q` norm terms and `npcRamOps h r` really contains the
exponents `±2^r`. Uniformity in those parameters is carried by the quantified signature
theorems below, not by the finite set of exported instances. The export selects no
coefficient module, marking, field, resolver, `eta`, or source certificate, and it is not an
approved appendix, manifest entry, gate or release.
-/

namespace GQ2.Dyadic.W362LNFox

open GQ2 GQ2.FoxH GQ2.Dyadic.Words GQ2.Dyadic.Certificates
open Export (jsonString intToString natToString)

/-! ## Names for the sector data that the records spell inline -/

/-- The L scalar branch's single row operation, spelled inline in `lSqJacobianCertScalar`. -/
def lSqScalarOps (h : ℕ) : List (FoxRowOp (TameSym (2*h+1))) := [.addSnd (.neg .one)]

/-- The L scalar branch's degenerate target, spelled inline in `lSqJacobianCertScalar`:
the tame pivot on `τ` over an identically zero wild row. -/
def lSqScalarNormalForm (h : ℕ) :
    FoxNormalForm (Generator (2*h+1)) (TameSym (2*h+1)) :=
  ⟨.single .tau, ⟨fun _ => .zero⟩⟩

/-- The Npc unramified target, spelled inline in `npcJacobianCertUnram`: the universal
unramified tame row over the honest two-entry block row. -/
def npcUnramNormalForm (h r : ℕ) :
    FoxNormalForm (Generator (2 + 2*h)) (Npc.NpcSym (2 + 2*h)) :=
  ⟨Npc.tameUnramRow _, Npc.npcBlockRow h r⟩

/-- The Npc ramified target, spelled inline in `npcJacobianCertRam`: the universal tame row
over the `x₂` unit pivot. -/
def npcRamNormalForm (h q : ℕ) :
    FoxNormalForm (Generator (2 + 2*h)) (Npc.NpcSym (2 + 2*h)) :=
  ⟨Npc.tameRow _ q, .single (Words.coreLetter h 2)⟩

/-! ## Signature theorems: the serialized values ARE the records' fields

Each is `rfl`. They are the only thing that makes the JSON below a statement about the
actual certificates rather than about freshly written data. -/

section LSignatures
variable {h q : ℕ} {C V : Type} [Group C] [Finite C] [AddCommGroup V] [Finite V]
  [DistribMulAction C V] (t : Marking (2*h+1) C) (E : Zhat → ℤ) (E2 : ℤ_[2] → ℤ)
  (hV2 : ∀ v : V, v+v=0) (hwild : ∀ (i : Fin (2*h+1+1)) (v : V), t.x i • v=v)

theorem lSqUnram_rowOps (htau : ∀ v : V, t.τ • v=v) (hqe : Even q) :
    (LSq.lSqJacobianCertUnram (q := q) t E E2 hV2 hwild htau hqe).rowOps
      = nCompactUnramOps (2*h+1) := rfl

theorem lSqUnram_colOps (htau : ∀ v : V, t.τ • v=v) (hqe : Even q) :
    (LSq.lSqJacobianCertUnram (q := q) t E E2 hV2 hwild htau hqe).colOps = [] := rfl

theorem lSqUnram_target (htau : ∀ v : V, t.τ • v=v) (hqe : Even q) :
    (LSq.lSqJacobianCertUnram (q := q) t E E2 hV2 hwild htau hqe).target
      = LSq.lSqUnramNormalForm h := rfl

theorem lSqRam_rowOps (hfpf : ∀ v : V, t.τ • v=v → v=0)
    (hodd : ∀ v : V, powOmega2 t.τ • v=v) (hrel : conjR t.τ t.σ = t.τ ^ q) :
    (LSq.lSqJacobianCertRam t E E2 hV2 hwild hfpf hodd hrel).rowOps = [] := rfl

theorem lSqRam_colOps (hfpf : ∀ v : V, t.τ • v=v → v=0)
    (hodd : ∀ v : V, powOmega2 t.τ • v=v) (hrel : conjR t.τ t.σ = t.τ ^ q) :
    (LSq.lSqJacobianCertRam t E E2 hV2 hwild hfpf hodd hrel).colOps = LSq.lSqRamOps h := rfl

theorem lSqRam_target (hfpf : ∀ v : V, t.τ • v=v → v=0)
    (hodd : ∀ v : V, powOmega2 t.τ • v=v) (hrel : conjR t.τ t.σ = t.τ ^ q) :
    (LSq.lSqJacobianCertRam t E E2 hV2 hwild hfpf hodd hrel).target
      = LSq.lSqRamNormalForm h q := rfl

theorem lSqScalar_rowOps (htau : ∀ v : V, t.τ • v=v) (hsigma : ∀ v : V, t.σ • v=v)
    (hqe : Even q) :
    (LSq.lSqJacobianCertScalar (q := q) t E E2 hV2 hwild htau hsigma hqe).rowOps
      = lSqScalarOps h := rfl

theorem lSqScalar_colOps (htau : ∀ v : V, t.τ • v=v) (hsigma : ∀ v : V, t.σ • v=v)
    (hqe : Even q) :
    (LSq.lSqJacobianCertScalar (q := q) t E E2 hV2 hwild htau hsigma hqe).colOps = [] := rfl

theorem lSqScalar_target (htau : ∀ v : V, t.τ • v=v) (hsigma : ∀ v : V, t.σ • v=v)
    (hqe : Even q) :
    (LSq.lSqJacobianCertScalar (q := q) t E E2 hV2 hwild htau hsigma hqe).target
      = lSqScalarNormalForm h := rfl

end LSignatures

section N0Signatures
variable {h alpha q : ℕ} {C V : Type} [Group C] [Finite C] [AddCommGroup V] [Finite V]
  [DistribMulAction C V] (t : Marking (2 + 2*h) C) (E : Zhat → ℤ) (E2 : ℤ_[2] → ℤ)
  (hV2 : ∀ v : V, v + v = 0)
  (hwild : ∀ (i : Fin (2 + 2*h + 1)) (v : V), t.x i • v = v)

theorem nCompactUnram_rowOps (htau : ∀ v : V, t.τ • v = v) (hq : Even q) (halpha : 1 ≤ alpha) :
    (nCompactJacobianCertUnram (α := alpha) t E E2 hV2 hwild htau hq halpha).rowOps
      = nCompactUnramOps (2 + 2*h) := rfl

theorem nCompactUnram_colOps (htau : ∀ v : V, t.τ • v = v) (hq : Even q) (halpha : 1 ≤ alpha) :
    (nCompactJacobianCertUnram (α := alpha) t E E2 hV2 hwild htau hq halpha).colOps = [] := rfl

theorem nCompactUnram_target (htau : ∀ v : V, t.τ • v = v) (hq : Even q) (halpha : 1 ≤ alpha) :
    (nCompactJacobianCertUnram (α := alpha) t E E2 hV2 hwild htau hq halpha).target
      = nCompactUnramNormalForm h := rfl

theorem nCompactRam_rowOps (hfpf : ∀ v : V, t.τ • v = v → v = 0)
    (hodd : ∀ v : V, powOmega2 t.τ • v = v) (hrel : conjR t.τ t.σ = t.τ ^ q)
    (halpha : 1 ≤ alpha) :
    (nCompactJacobianCertRam (α := alpha) t E E2 hV2 hwild hfpf hodd hrel halpha).rowOps
      = [] := rfl

theorem nCompactRam_colOps (hfpf : ∀ v : V, t.τ • v = v → v = 0)
    (hodd : ∀ v : V, powOmega2 t.τ • v = v) (hrel : conjR t.τ t.σ = t.τ ^ q)
    (halpha : 1 ≤ alpha) :
    (nCompactJacobianCertRam (α := alpha) t E E2 hV2 hwild hfpf hodd hrel halpha).colOps
      = nCompactRamOps h := rfl

theorem nCompactRam_target (hfpf : ∀ v : V, t.τ • v = v → v = 0)
    (hodd : ∀ v : V, powOmega2 t.τ • v = v) (hrel : conjR t.τ t.σ = t.τ ^ q)
    (halpha : 1 ≤ alpha) :
    (nCompactJacobianCertRam (α := alpha) t E E2 hV2 hwild hfpf hodd hrel halpha).target
      = nCompactRamNormalForm h q := rfl

end N0Signatures

section NpcSignatures
variable {h alpha r q : ℕ} {C V : Type} [Group C] [Finite C] [AddCommGroup V] [Finite V]
  [DistribMulAction C V] (t : Marking (2 + 2*h) C) (E : Zhat → ℤ) (E2 : ℤ_[2] → ℤ)
  (hV2 : ∀ v : V, v + v = 0)
  (hwild : ∀ (i : Fin (2 + 2*h + 1)) (v : V), t.x i • v = v)

theorem npcUnram_rowOps (htau : ∀ v : V, t.τ • v = v) (hq : Even q) (halpha : 1 ≤ alpha)
    (e : EtaData) :
    (Npc.npcJacobianCertUnram (α := alpha) (r := r) t E E2 hV2 hwild htau hq halpha e).rowOps
      = Npc.npcUnramOps (2 + 2*h) := rfl

theorem npcUnram_colOps (htau : ∀ v : V, t.τ • v = v) (hq : Even q) (halpha : 1 ≤ alpha)
    (e : EtaData) :
    (Npc.npcJacobianCertUnram (α := alpha) (r := r) t E E2 hV2 hwild htau hq halpha e).colOps
      = [] := rfl

theorem npcUnram_target (htau : ∀ v : V, t.τ • v = v) (hq : Even q) (halpha : 1 ≤ alpha)
    (e : EtaData) :
    (Npc.npcJacobianCertUnram (α := alpha) (r := r) t E E2 hV2 hwild htau hq halpha e).target
      = npcUnramNormalForm h r := rfl

theorem npcRam_rowOps (hfpf : ∀ v : V, t.τ • v = v → v = 0)
    (hodd : ∀ v : V, powOmega2 t.τ • v = v) (hrel : conjR t.τ t.σ = t.τ ^ q)
    (halpha : 1 ≤ alpha) (e : EtaData) :
    (Npc.npcJacobianCertRam (α := alpha) (r := r) t E E2 hV2 hwild hfpf hodd hrel halpha e).rowOps
      = [] := rfl

theorem npcRam_colOps (hfpf : ∀ v : V, t.τ • v = v → v = 0)
    (hodd : ∀ v : V, powOmega2 t.τ • v = v) (hrel : conjR t.τ t.σ = t.τ ^ q)
    (halpha : 1 ≤ alpha) (e : EtaData) :
    (Npc.npcJacobianCertRam (α := alpha) (r := r) t E E2 hV2 hwild hfpf hodd hrel halpha e).colOps
      = Npc.npcRamOps h r := rfl

theorem npcRam_target (hfpf : ∀ v : V, t.τ • v = v → v = 0)
    (hodd : ∀ v : V, powOmega2 t.τ • v = v) (hrel : conjR t.τ t.σ = t.τ ^ q)
    (halpha : 1 ≤ alpha) (e : EtaData) :
    (Npc.npcJacobianCertRam (α := alpha) (r := r) t E E2 hV2 hwild hfpf hodd hrel halpha e).target
      = npcRamNormalForm h q := rfl

end NpcSignatures

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

def rowOpJson {S : Type} (atom : S → String) : FoxRowOp S → String
  | .swap => "{\"op\":\"swap\"}"
  | .addFst c => "{\"coefficient\":" ++ coeffJson atom c ++ ",\"op\":\"add_fst\"}"
  | .addSnd c => "{\"coefficient\":" ++ coeffJson atom c ++ ",\"op\":\"add_snd\"}"
  | .scaleFst c d => "{\"forward\":" ++ coeffJson atom c ++ ",\"inverse\":" ++
      coeffJson atom d ++ ",\"op\":\"scale_fst\"}"
  | .scaleSnd c d => "{\"forward\":" ++ coeffJson atom c ++ ",\"inverse\":" ++
      coeffJson atom d ++ ",\"op\":\"scale_snd\"}"

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

def normalFormJson {n : ℕ} {S : Type} (atom : S → String)
    (nf : FoxNormalForm (Generator n) S) : String :=
  "{\"fst\":" ++ rowJson atom nf.fst ++ ",\"snd\":" ++ rowJson atom nf.snd ++ "}"

def bridgesJson (colName rowName targetName : String) : String :=
  "{\"column_operations\":" ++ jsonString colName ++ ",\"row_operations\":" ++
    jsonString rowName ++ ",\"target\":" ++ jsonString targetName ++ "}"

def sectorJson {n : ℕ} {S : Type} (atom : S → String) (name record alphabet : String)
    (bridges : String) (rowOps : List (FoxRowOp S))
    (colOps : List (FoxColOp (Generator n) S))
    (target : FoxNormalForm (Generator n) S) : String :=
  "{\"column_operations\":" ++ bracket (colOps.map (colOpJson atom)) ++
  ",\"record\":" ++ jsonString record ++
  ",\"row_operations\":" ++ bracket (rowOps.map (rowOpJson atom)) ++
  ",\"sector\":" ++ jsonString name ++
  ",\"signature_bridges\":" ++ bridges ++
  ",\"symbol_alphabet\":" ++ jsonString alphabet ++
  ",\"target\":" ++ normalFormJson atom target ++ "}"

def schema : String := "gq2.w362.ln-fox.v1.staged"
def hashDomain : String := "GQ2-W362-LN-FOX\x00"
def certRoot : String := "GQ2.Dyadic.Certificates."
def bridgeRoot : String := "GQ2.Dyadic.W362LNFox."

def scopeNote : String :=
  "Ledger items 4 and 5 only, for the existing L/N0/Npc FoxCertificate records under their own stated hypotheses. No coefficient module, marking, field, resolver, eta or source certificate is selected."

def compositionNote : String :=
  "Row list applies head first; column list denotes head composed with tail; comp(outer,inner) applies inner first. Every scale carries its formal inverse as data."

def hashScopeNote : String :=
  "Identity of the serialized operation lists and normal matrices at the stated discrete parameters. Uniformity in h, q and r is carried by the rfl signature theorems, not by this instance."

def lSectors (h q : ℕ) : List String :=
  [ sectorJson tameSymJson "unramified" (certRoot ++ "LSq.lSqJacobianCertUnram") "TameSym"
      (bridgesJson (bridgeRoot ++ "lSqUnram_colOps") (bridgeRoot ++ "lSqUnram_rowOps")
        (bridgeRoot ++ "lSqUnram_target"))
      (nCompactUnramOps (2*h+1)) [] (LSq.lSqUnramNormalForm h)
  , sectorJson tameSymJson "ramified" (certRoot ++ "LSq.lSqJacobianCertRam") "TameSym"
      (bridgesJson (bridgeRoot ++ "lSqRam_colOps") (bridgeRoot ++ "lSqRam_rowOps")
        (bridgeRoot ++ "lSqRam_target"))
      [] (LSq.lSqRamOps h) (LSq.lSqRamNormalForm h q)
  , sectorJson tameSymJson "scalar" (certRoot ++ "LSq.lSqJacobianCertScalar") "TameSym"
      (bridgesJson (bridgeRoot ++ "lSqScalar_colOps") (bridgeRoot ++ "lSqScalar_rowOps")
        (bridgeRoot ++ "lSqScalar_target"))
      (lSqScalarOps h) [] (lSqScalarNormalForm h) ]

def n0Sectors (h q : ℕ) : List String :=
  [ sectorJson tameSymJson "unramified" (certRoot ++ "nCompactJacobianCertUnram") "TameSym"
      (bridgesJson (bridgeRoot ++ "nCompactUnram_colOps") (bridgeRoot ++ "nCompactUnram_rowOps")
        (bridgeRoot ++ "nCompactUnram_target"))
      (nCompactUnramOps (2 + 2*h)) [] (nCompactUnramNormalForm h)
  , sectorJson tameSymJson "ramified" (certRoot ++ "nCompactJacobianCertRam") "TameSym"
      (bridgesJson (bridgeRoot ++ "nCompactRam_colOps") (bridgeRoot ++ "nCompactRam_rowOps")
        (bridgeRoot ++ "nCompactRam_target"))
      [] (nCompactRamOps h) (nCompactRamNormalForm h q) ]

def npcSectors (h r q : ℕ) : List String :=
  [ sectorJson npcSymJson "unramified" (certRoot ++ "Npc.npcJacobianCertUnram") "NpcSym"
      (bridgesJson (bridgeRoot ++ "npcUnram_colOps") (bridgeRoot ++ "npcUnram_rowOps")
        (bridgeRoot ++ "npcUnram_target"))
      (Npc.npcUnramOps (2 + 2*h)) [] (npcUnramNormalForm h r)
  , sectorJson npcSymJson "ramified" (certRoot ++ "Npc.npcJacobianCertRam") "NpcSym"
      (bridgesJson (bridgeRoot ++ "npcRam_colOps") (bridgeRoot ++ "npcRam_rowOps")
        (bridgeRoot ++ "npcRam_target"))
      [] (Npc.npcRamOps h r) (npcRamNormalForm h q) ]

def payload (family : String) (n h : ℕ) (structural : String)
    (sectors : List String) : String :=
  "{\"alphabet\":{\"degree\":" ++ natToString n ++ ",\"h\":" ++ natToString h ++
    ",\"wild_count\":" ++ natToString (n+1) ++ "}," ++
  "\"application_scope\":" ++ jsonString scopeNote ++ "," ++
  "\"composition\":" ++ jsonString compositionNote ++ "," ++
  "\"family\":" ++ jsonString family ++ "," ++
  "\"hash_scope\":" ++ jsonString hashScopeNote ++ "," ++
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
    | ["Npc", hs, rs, qs] => match hs.toNat?, rs.toNat?, qs.toNat? with
      | some h, some r, some q =>
          pure (payload "Npc" (2+2*h) h (structuralNpc h q r) (npcSectors h r q))
      | _, _, _ => throw (IO.userError "Npc H R Q: H, R and Q must be natural numbers")
    | _ => throw (IO.userError "usage: L H Q | N0 H Q | Npc H R Q")
  IO.println ("W362_LN_FOX_JSON=" ++ envelope p)

#print axioms lSqUnram_rowOps
#print axioms lSqUnram_colOps
#print axioms lSqUnram_target
#print axioms lSqRam_rowOps
#print axioms lSqRam_colOps
#print axioms lSqRam_target
#print axioms lSqScalar_rowOps
#print axioms lSqScalar_colOps
#print axioms lSqScalar_target
#print axioms nCompactUnram_rowOps
#print axioms nCompactUnram_colOps
#print axioms nCompactUnram_target
#print axioms nCompactRam_rowOps
#print axioms nCompactRam_colOps
#print axioms nCompactRam_target
#print axioms npcUnram_rowOps
#print axioms npcUnram_colOps
#print axioms npcUnram_target
#print axioms npcRam_rowOps
#print axioms npcRam_colOps
#print axioms npcRam_target
#print axioms lSqScalarOps
#print axioms lSqScalarNormalForm
#print axioms npcUnramNormalForm
#print axioms npcRamNormalForm
#print axioms exportMain

end GQ2.Dyadic.W362LNFox

def main (args : List String) : IO Unit := GQ2.Dyadic.W362LNFox.exportMain args
