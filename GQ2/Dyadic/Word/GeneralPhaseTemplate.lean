/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, and OpenAI Codex
-/
import GQ2.Dyadic.Word.Export
import GQ2.Dyadic.Instances.WordPhaseCompactCertificates

/-!
# STAGED typed compact quadratic-phase templates

The finite computable tree is the object serialized to JSON. Its denotation is proved
equal to the existing compact wall-handle phase for every rank, additive coefficient
group and function q. The source-comparison and original phase-cover bridges retain the
actual full quadratic phase, not just its polarization or Gauss value.

This separate format changes neither frozen word syntax nor original certificate records.
The coefficient matrices are serialized directly from the previously proved matrix
definitions. They are coefficients relative to the polar q pairing, not a claim that
that pairing itself is the identity matrix. No executable main is declared in this library.
-/

namespace GQ2.Dyadic.GeneralPhaseTemplate
open GQ2 GQ2.Dyadic GQ2.QuadraticFp2
open Instances.WordPhase Instances.WordPhasePolarNormal Instances.WordPhaseCompactCertificates

/-- The finite phase-coordinate alphabet, indexed by the actual number of handles. -/
inductive Coordinate (h : ℕ) where
  | head0
  | head1
  | handleU (j : Fin h)
  | handleV (j : Fin h)
  deriving Repr, DecidableEq

/-- A typed quadratic expression. The ordered handle tail uses the same add constructor. -/
inductive Tree (h : ℕ) where
  | zero
  | baseQuad (x : Coordinate h)
  | polar (x y : Coordinate h)
  | add (left right : Tree h)
  deriving Repr

def Coordinate.denote {h : ℕ} {V : Type} (p : CompactCoordinates V h) : Coordinate h → V
  | .head0 => p.1.1
  | .head1 => p.1.2
  | .handleU j => (p.2 j).1
  | .handleV j => (p.2 j).2

def Tree.denote {h : ℕ} {V : Type} [AddCommGroup V] (q : V → ZMod 2)
    (p : CompactCoordinates V h) : Tree h → ZMod 2
  | .zero => 0
  | .baseQuad x => q (x.denote p)
  | .polar x y => QuadraticFp2.polar q (x.denote p) (y.denote p)
  | .add a b => a.denote q p + b.denote q p

def Tree.sumList {h : ℕ} : List (Tree h) → Tree h
  | [] => .zero
  | x :: xs => .add x (sumList xs)

theorem Tree.denote_sumList {h : ℕ} {V : Type} [AddCommGroup V]
    (q : V → ZMod 2) (p : CompactCoordinates V h) (xs : List (Tree h)) :
    (Tree.sumList xs).denote q p = (xs.map (Tree.denote q p)).sum := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [Tree.sumList, Tree.denote, List.map_cons, List.sum_cons, ih]

/-- The exact ordered expression `q(head0)+Bq(head0,head1)+sum Bq(handleU,handleV)`. -/
def compactPhase (h : ℕ) : Tree h :=
  .add (.add (.baseQuad .head0) (.polar .head0 .head1))
    (Tree.sumList (List.ofFn fun j : Fin h => Tree.polar (.handleU j) (.handleV j)))

/-- Rank-uniform literal denotation bridge; quadraticity of q is not needed for equality. -/
theorem denote_compactPhase {V : Type} [AddCommGroup V]
    (q : V → ZMod 2) (h : ℕ) (p : CompactCoordinates V h) :
    (compactPhase h).denote q p = wPhCompactWallHandlePhase q h p := by
  simp only [compactPhase, Tree.denote, Coordinate.denote, Tree.denote_sumList,
    List.map_ofFn, List.sum_ofFn, Function.comp_apply,
    wPhCompactWallHandlePhase, plusFormD]

/-- The tree's polar matrix is exactly the already certified rank-uniform matrix. -/
theorem polar_denote_compactPhase {V : Type} [AddCommGroup V]
    (q : V → ZMod 2) (hq : IsQuadraticFp2 q) (h : ℕ)
    (x y : CompactCoordinates V h) :
    polar (fun p => (compactPhase h).denote q p) x y =
      ∑ i, ∑ j, reducedCoefficientMatrix h i j *
        polar q (blockCoordinates h x i) (blockCoordinates h y j) := by
  simp only [denote_compactPhase]
  exact polar_compactPhase_reducedMatrix q hq h x y

/-- Existing original phase-cover data, with its endpoint written as the exported tree. -/
noncomputable def compactPhaseCover_tree {C V : Type} [Group C] [AddCommGroup V]
    [DistribMulAction C V] [Fintype V] {q : V → ZMod 2}
    (dat : FactorSet C V) (hdat : IsEquivariantFactorSet q dat)
    (hq : IsQuadraticFp2 q) (hns : Nonsingular q) {d : ℕ}
    (hcard : Fintype.card V = 2^d) (h : ℕ) :
    PhaseCoverCertificate dat (fun v => dat.f v v)
      (fun p => (compactPhase h).denote q p) (headDiagonal h) (headCross h) := by
  simpa only [denote_compactPhase] using compactPhaseCover dat hdat hq hns hcard h

section Source
open GQ2.SectionEight SectionSeven AffineTLift CentralObstruction ContCoh
open GQ2.Dyadic.LSquare
variable {Bg : Type} [Group Bg] [Finite Bg] [TopologicalSpace Bg] [DiscreteTopology Bg]
  {D : RadicalCoverData Bg} {DD : DescData D}
  {Gamma : Type} [Group Gamma] [TopologicalSpace Gamma]
  {rho : ContinuousMonoidHom Gamma (Bg ⧸ D.M)}
  [DistribMulAction Gamma (ZMod 2)]
  {htriv : ∀ (g : Gamma) (a : ZMod 2), g • a=a}
  {h : ℕ} [Fintype DD.Vmod]

/-- A source comparison is tied to this exact tree using its unchanged coordinate map.
This applies to the actual pair/mobile comparisons, not to a newly chosen isometry. -/
theorem sourcePhase_eq_denote
    (C : SourceWordPhaseComparison DD rho htriv (CompactCoordinates DD.Vmod h)
      (wPhCompactWallHandlePhase DD.qbar h))
    (x : VCocycle DD rho ⧸ vCobRange DD rho) :
    QZeroBar DD rho htriv x = (compactPhase h).denote DD.qbar (C.phaseEquiv x) := by
  rw [denote_compactPhase]
  exact C.phase_eq x

/-- The original source Hessian record's actual linear map has the same tree-valued phase. -/
theorem sourceHessian_cov_eq_denote
    (C : SourceWordPhaseComparison DD rho htriv (CompactCoordinates DD.Vmod h)
      (wPhCompactWallHandlePhase DD.qbar h))
    (hadd : ∀ x y, C.phaseEquiv (x+y)=C.phaseEquiv x+C.phaseEquiv y)
    (x : VCocycle DD rho ⧸ vCobRange DD rho) :
    letI : Module (ZMod 2) DD.Vmod := AddCommGroup.zmodModule
      (fun v => (two_nsmul v).trans (Vmod_exp2 DD v))
    letI := sourceQuotientModule DD rho
    QZeroBar DD rho htriv x = (compactPhase h).denote DD.qbar
      ((sourceCompactHessianOfComparison DD rho htriv C hadd).cov x) :=
  sourcePhase_eq_denote C x
end Source

/-- Each exported coordinate names the exact index of the proved polar matrix. -/
def Coordinate.blockIndex {h : ℕ} : Coordinate h → BlockIndex h
  | .head0 => .inl 0
  | .head1 => .inl 1
  | .handleU j => .inr (j, 0)
  | .handleV j => .inr (j, 1)

theorem Coordinate.denote_eq_blockCoordinates {h : ℕ} {V : Type} [AddCommGroup V]
    (p : CompactCoordinates V h) (c : Coordinate h) :
    c.denote p = blockCoordinates h p c.blockIndex := by
  cases c <;> rfl

/-- The explicit complete row/column ordering, with increasing handle indices. -/
def coordinateList (h : ℕ) : List (Coordinate h) :=
  [.head0, .head1] ++ (List.ofFn fun j : Fin h =>
    [Coordinate.handleU j, Coordinate.handleV j]).flatten

theorem mem_coordinateList {h : ℕ} (c : Coordinate h) : c ∈ coordinateList h := by
  cases c <;> simp [coordinateList, List.mem_flatten]

theorem coordinateList_length (h : ℕ) : (coordinateList h).length = 2+2*h := by
  simp [coordinateList, List.length_flatten, List.map_ofFn, List.sum_ofFn, Nat.mul_comm]
  omega

open GQ2.Dyadic.Export (jsonString natToString)

def Coordinate.toJson {h : ℕ} : Coordinate h → String
  | .head0 => "{\"coordinate\":\"head0\"}"
  | .head1 => "{\"coordinate\":\"head1\"}"
  | .handleU j => "{\"coordinate\":\"handleU\",\"index\":" ++ natToString j.val ++ "}"
  | .handleV j => "{\"coordinate\":\"handleV\",\"index\":" ++ natToString j.val ++ "}"

/-- Direct traversal of the same finite tree used in the denotation theorem. -/
def Tree.toJson {h : ℕ} : Tree h → String
  | .zero => "{\"op\":\"zero\"}"
  | .baseQuad x => "{\"at\":" ++ x.toJson ++ ",\"op\":\"baseQuad\"}"
  | .polar x y => "{\"left\":" ++ x.toJson ++ ",\"op\":\"polar\",\"right\":" ++ y.toJson ++ "}"
  | .add a b => "{\"left\":" ++ a.toJson ++ ",\"op\":\"add\",\"right\":" ++ b.toJson ++ "}"

private def jsonArray (xs : List String) : String := "[" ++ String.intercalate "," xs ++ "]"

/-- Serializes existing matrix entries, without a second hand-entered matrix formula. -/
def matrixJson (h : ℕ) (M : Matrix (BlockIndex h) (BlockIndex h) (ZMod 2)) : String :=
  jsonArray ((coordinateList h).map fun i => jsonArray ((coordinateList h).map fun j =>
    natToString (M i.blockIndex j.blockIndex).val))

def stagedSchema : String := "gq2.w361.quadratic-phase.v1.staged"
def hashDomain : String := "GQ2-W361-QUADRATIC-PHASE\x00"

/-- Canonical data payload. Matrices are relative to Bq, and all q-values stay symbolic. -/
def compactPayload (h : ℕ) : String :=
  "{\"bridge\":\"GQ2.Dyadic.GeneralPhaseTemplate.denote_compactPhase\",\"coordinates\":" ++
    jsonArray ((coordinateList h).map Coordinate.toJson) ++
    ",\"factory\":\"GQ2.Dyadic.GeneralPhaseTemplate.compactPhase\",\"inverse_matrix\":" ++
    matrixJson h (reducedInverseMatrix h) ++
    ",\"kind\":\"compact-wall-handle\",\"matrix\":" ++
    matrixJson h (reducedCoefficientMatrix h) ++
    ",\"pairing\":\"polar(q)\",\"schema\":" ++ jsonString stagedSchema ++
    ",\"structural\":{\"h\":" ++ natToString h ++ "},\"tree\":" ++
    (compactPhase h).toJson ++ "}"

def payloadHash (canonicalPayload : String) : String :=
  Export.Sha256.hex (hashDomain ++ canonicalPayload)

def envelope (canonicalPayload : String) : String :=
  "{\"payload\":" ++ canonicalPayload ++ ",\"status\":\"STAGED\",\"template_hash\":" ++
    jsonString (payloadHash canonicalPayload) ++ "}"

#print axioms Coordinate.denote
#print axioms Tree.denote
#print axioms Tree.sumList
#print axioms Tree.denote_sumList
#print axioms compactPhase
#print axioms denote_compactPhase
#print axioms polar_denote_compactPhase
#print axioms compactPhaseCover_tree
#print axioms sourcePhase_eq_denote
#print axioms sourceHessian_cov_eq_denote
#print axioms Coordinate.blockIndex
#print axioms Coordinate.denote_eq_blockCoordinates
#print axioms coordinateList
#print axioms mem_coordinateList
#print axioms coordinateList_length
#print axioms Coordinate.toJson
#print axioms Tree.toJson
#print axioms matrixJson
#print axioms stagedSchema
#print axioms hashDomain
#print axioms compactPayload
#print axioms payloadHash
#print axioms envelope

end GQ2.Dyadic.GeneralPhaseTemplate
