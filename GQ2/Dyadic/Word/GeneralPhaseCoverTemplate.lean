/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, and OpenAI Codex
-/
import GQ2.Dyadic.Word.GeneralPhaseTemplate

/-!
# STAGED typed data for the compact phase-cover certificate

This computable template exports the actual two head embeddings, full quadratic
diagonal, positive sign, and dimension expression with coefficient dimension left
symbolic. The field-agreement theorem identifies it with the existing original
`compactPhaseCover`; it is not a replacement certificate or an unconditional
certificate for arbitrary serialized data. The accompanying phase tree is the
same tree already tied to actual source comparisons in `GeneralPhaseTemplate`.
-/

namespace GQ2.Dyadic.GeneralPhaseCoverTemplate
open GQ2 GQ2.Dyadic GQ2.QuadraticFp2
open GeneralPhaseTemplate
open Instances.WordPhase Instances.WordPhasePolarNormal Instances.WordPhaseCompactCertificates

/-- An embedding coordinate is either zero or its one input vector. -/
inductive InputTerm where
  | zero
  | input
  deriving Repr, DecidableEq

def InputTerm.denote {V : Type} [Zero V] (v : V) : InputTerm → V
  | .zero => 0
  | .input => v

/-- A typed coordinate table, whose indices use the actual handle rank. -/
abbrev Embedding (h : ℕ) := Coordinate h → InputTerm

def Embedding.denote {h : ℕ} {V : Type} [Zero V] (e : Embedding h) (v : V) :
    CompactCoordinates V h :=
  ((e .head0 |>.denote v, e .head1 |>.denote v),
    fun j => (e (.handleU j) |>.denote v, e (.handleV j) |>.denote v))

def diagonalEmbedding (h : ℕ) : Embedding h
  | .head0 => .input
  | _ => .zero

def crossEmbedding (h : ℕ) : Embedding h
  | .head1 => .input
  | _ => .zero

/-- The coefficient dimension remains a symbolic natural variable. -/
inductive DimensionTerm where
  | literal (n : ℕ)
  | dimension
  | add (left right : DimensionTerm)
  | mul (left right : DimensionTerm)
  deriving Repr, DecidableEq

def DimensionTerm.denote (d : ℕ) : DimensionTerm → ℕ
  | .literal n => n
  | .dimension => d
  | .add a b => a.denote d + b.denote d
  | .mul a b => a.denote d * b.denote d

/-- A quadratic diagonal, retaining q rather than only its polar pairing. -/
inductive DiagonalTerm where
  | baseQuad (term : InputTerm)
  deriving Repr, DecidableEq

def DiagonalTerm.denote {V : Type} [Zero V] (q : V → ZMod 2) (v : V) :
    DiagonalTerm → ZMod 2
  | .baseQuad term => q (term.denote v)

/-- Computable publication data, not a replacement for `PhaseCoverCertificate`. -/
structure Template (h : ℕ) where
  phase : Tree h
  j0 : Embedding h
  j1 : Embedding h
  diagonal : DiagonalTerm
  baseDim : DimensionTerm
  baseSign : ℤ

def compactTemplate (h : ℕ) : Template h where
  phase := compactPhase h
  j0 := diagonalEmbedding h
  j1 := crossEmbedding h
  diagonal := .baseQuad .input
  baseDim := .mul (.add (.literal h) (.literal 1)) .dimension
  baseSign := 1

theorem diagonalEmbedding_denote {V : Type} [AddCommGroup V] (h : ℕ) (v : V) :
    (diagonalEmbedding h).denote v = headDiagonal h v := rfl

theorem crossEmbedding_denote {V : Type} [AddCommGroup V] (h : ℕ) (v : V) :
    (crossEmbedding h).denote v = headCross h v := rfl

theorem compactTemplate_phase {V : Type} [AddCommGroup V]
    (q : V → ZMod 2) (h : ℕ) (p : CompactCoordinates V h) :
    (compactTemplate h).phase.denote q p = wPhCompactWallHandlePhase q h p :=
  denote_compactPhase q h p

/-- Literal data agreement with the original all-rank phase-cover certificate.
The assumptions are exactly the existing cover's quadratic, nonsingular and
cardinality hypotheses, and the actual equivariant factor set. -/
theorem compactTemplate_agrees {C V : Type} [Group C] [AddCommGroup V]
    [DistribMulAction C V] [Fintype V] {q : V → ZMod 2}
    (dat : FactorSet C V) (hdat : IsEquivariantFactorSet q dat)
    (hq : IsQuadraticFp2 q) (hns : Nonsingular q) {d : ℕ}
    (hcard : Fintype.card V = 2^d) (h : ℕ) :
    (∀ p, (compactTemplate h).phase.denote q p = wPhCompactWallHandlePhase q h p) ∧
    (∀ v : V, (compactTemplate h).j0.denote v = headDiagonal h v) ∧
    (∀ v : V, (compactTemplate h).j1.denote v = headCross h v) ∧
    (∀ v : V, (compactTemplate h).diagonal.denote q v = dat.f v v) ∧
    (compactTemplate h).baseDim.denote d =
      (compactPhaseCover dat hdat hq hns hcard h).baseDim ∧
    (compactTemplate h).baseSign =
      (compactPhaseCover dat hdat hq hns hcard h).baseSign := by
  refine ⟨compactTemplate_phase q h, diagonalEmbedding_denote h,
    crossEmbedding_denote h, ?_, rfl, rfl⟩
  intro v
  exact (hdat.f_diag v).symm

open GQ2.Dyadic.Export (jsonString natToString)

def InputTerm.toJson : InputTerm → String
  | .zero => "{\"op\":\"zero\"}"
  | .input => "{\"op\":\"input\"}"

private def jsonArray (xs : List String) : String := "[" ++ String.intercalate "," xs ++ "]"

def Embedding.toJson {h : ℕ} (e : Embedding h) : String :=
  jsonArray ((coordinateList h).map fun c =>
    "{\"at\":" ++ c.toJson ++ ",\"value\":" ++ (e c).toJson ++ "}")

def DimensionTerm.toJson : DimensionTerm → String
  | .literal n => "{\"op\":\"literal\",\"value\":" ++ natToString n ++ "}"
  | .dimension => "{\"op\":\"dimension\",\"variable\":\"d\"}"
  | .add a b => "{\"left\":" ++ a.toJson ++ ",\"op\":\"add\",\"right\":" ++ b.toJson ++ "}"
  | .mul a b => "{\"left\":" ++ a.toJson ++ ",\"op\":\"mul\",\"right\":" ++ b.toJson ++ "}"

def DiagonalTerm.toJson : DiagonalTerm → String
  | .baseQuad term => "{\"at\":" ++ term.toJson ++ ",\"op\":\"baseQuad\"}"

def stagedSchema : String := "gq2.w361.phase-cover.v1.staged"
def hashDomain : String := "GQ2-W361-PHASE-COVER\x00"

/-- Canonical payload serialized from the one typed template. The phase hash is
the exact separately exported phase-and-matrix payload's hash, not a source hash. -/
def compactPayload (h : ℕ) : String :=
  let t := compactTemplate h
  "{\"base_dim\":" ++ t.baseDim.toJson ++
    ",\"base_sign\":" ++ toString t.baseSign ++
    ",\"bridge\":\"GQ2.Dyadic.GeneralPhaseCoverTemplate.compactTemplate_agrees\"" ++
    ",\"diagonal\":" ++ t.diagonal.toJson ++
    ",\"factory\":\"GQ2.Dyadic.GeneralPhaseCoverTemplate.compactTemplate\"" ++
    ",\"j0\":" ++ t.j0.toJson ++ ",\"j1\":" ++ t.j1.toJson ++
    ",\"kind\":\"compact-wall-handle\",\"phase_template_hash\":" ++
    jsonString (GeneralPhaseTemplate.payloadHash (GeneralPhaseTemplate.compactPayload h)) ++
    ",\"phase_tree\":" ++ t.phase.toJson ++
    ",\"schema\":" ++ jsonString stagedSchema ++
    ",\"structural\":{\"h\":" ++ natToString h ++ "}}"

def payloadHash (canonicalPayload : String) : String :=
  Export.Sha256.hex (hashDomain ++ canonicalPayload)

def envelope (canonicalPayload : String) : String :=
  "{\"payload\":" ++ canonicalPayload ++ ",\"status\":\"STAGED\",\"template_hash\":" ++
    jsonString (payloadHash canonicalPayload) ++ "}"

#print axioms InputTerm.denote
#print axioms Embedding.denote
#print axioms diagonalEmbedding
#print axioms crossEmbedding
#print axioms DimensionTerm.denote
#print axioms DiagonalTerm.denote
#print axioms compactTemplate
#print axioms diagonalEmbedding_denote
#print axioms crossEmbedding_denote
#print axioms compactTemplate_phase
#print axioms compactTemplate_agrees
#print axioms InputTerm.toJson
#print axioms Embedding.toJson
#print axioms DimensionTerm.toJson
#print axioms DiagonalTerm.toJson
#print axioms stagedSchema
#print axioms hashDomain
#print axioms compactPayload
#print axioms payloadHash
#print axioms envelope

end GQ2.Dyadic.GeneralPhaseCoverTemplate
