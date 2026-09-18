/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, and OpenAI Codex
-/
import GQ2.Dyadic.Instances.TameSpliceRamifiedPolynomialFoxCertificates

/-!
# STAGED typed symbolic original-Fox operation templates

This additive schema leaves the original coefficient and operation grammar
unchanged. Its two finite-sum nodes expand at natural parameters q and k into
literal original coefficient expressions, including the carried formal inverses.
All three profile denotations are equal to the existing operation lists for EVERY
q and k. In actual certified uses, q is the source residue size and k is derived
from the coefficient action order; arbitrary instantiation is not a certificate.
No finite action order or coefficient space is selected by this syntax layer.
-/

namespace GQ2.Dyadic.GeneralFoxTemplate
open GQ2
open Instances.TameSplicePolynomialFoxCertificates
open Instances.TameSpliceRamifiedPolynomialFoxCertificates

/-- STAGED coefficient syntax. `oddSum` is expanded at k; `normSum` at q.
These are finite-sum templates, not new atoms of the original Fox grammar. -/
inductive Coeff (n : ℕ) where
  | zero
  | one
  | atom (symbol : TameSym n)
  | add (left right : Coeff n)
  | neg (value : Coeff n)
  | comp (outer inner : Coeff n)
  | oddSum (generator : Generator n) (sign : ℤ)
  | normSum (generator : Generator n)
  deriving Repr, DecidableEq

/-- Denotation expands the finite sums into the literal original coefficient tree. -/
def Coeff.denote {n : ℕ} (q k : ℕ) : Coeff n → FoxCoeff (TameSym n)
  | .zero => .zero
  | .one => .one
  | .atom s => .atom s
  | .add x y => .add (x.denote q k) (y.denote q k)
  | .neg x => .neg (x.denote q k)
  | .comp x y => .comp (x.denote q k) (y.denote q k)
  | .oddSum g sign => oddPowerCoeff g sign k
  | .normSum g => normPowerCoeff g q

inductive RowOp (n : ℕ) where
  | swap
  | addFst (coefficient : Coeff n)
  | addSnd (coefficient : Coeff n)
  | scaleFst (forward inverse : Coeff n)
  | scaleSnd (forward inverse : Coeff n)
  deriving Repr, DecidableEq

def RowOp.denote {n : ℕ} (q k : ℕ) : RowOp n → FoxRowOp (TameSym n)
  | .swap => .swap
  | .addFst c => .addFst (c.denote q k)
  | .addSnd c => .addSnd (c.denote q k)
  | .scaleFst c d => .scaleFst (c.denote q k) (d.denote q k)
  | .scaleSnd c d => .scaleSnd (c.denote q k) (d.denote q k)

inductive ColOp (n : ℕ) where
  | swap (left right : Generator n)
  | transvect (target source : Generator n) (coefficient : Coeff n)
  | scale (generator : Generator n) (forward inverse : Coeff n)
  deriving Repr, DecidableEq

def ColOp.denote {n : ℕ} (q k : ℕ) : ColOp n → FoxColOp (Generator n) (TameSym n)
  | .swap g h => .swap g h
  | .transvect g h c => .transvect g h (c.denote q k)
  | .scale g c d => .scale g (c.denote q k) (d.denote q k)

inductive PivotRow (n : ℕ) where
  | zero
  | single (generator : Generator n)
  deriving Repr, DecidableEq

def PivotRow.denote {n : ℕ} : PivotRow n → FoxRowNormalForm (Generator n) (TameSym n)
  | .zero => ⟨fun _ => .zero⟩
  | .single g => .single g

/-- Typed input-row expressions; addition order and coefficient placement are retained. -/
inductive LinearRow (n : ℕ) where
  | zero
  | term (coefficient : Coeff n) (generator : Generator n)
  | add (left right : LinearRow n)
  deriving Repr, DecidableEq

def LinearRow.denote {n : ℕ} (q k : ℕ) :
    LinearRow n → FoxRowNormalForm (Generator n) (TameSym n)
  | .zero => ⟨fun _ => .zero⟩
  | .term c g => ⟨fun j => if j=g then c.denote q k else .zero⟩
  | .add x y => ⟨fun j => .add ((x.denote q k).row j) ((y.denote q k).row j)⟩

def LinearRow.eval {n : ℕ} {A : Type*} [AddCommGroup A]
    (rho : TameSym n → AddMonoid.End A) (q k : ℕ) (x : Generator n → A) : LinearRow n → A
  | .zero => 0
  | .term c g => (c.denote q k).eval rho (x g)
  | .add a b => a.eval rho q k x + b.eval rho q k x

theorem LinearRow.denote_toHom_apply {n : ℕ} {A : Type*} [AddCommGroup A]
    (rho : TameSym n → AddMonoid.End A) (q k : ℕ) (x : Generator n → A) (r : LinearRow n) :
    (r.denote q k).toHom rho x = r.eval rho q k x := by
  induction r with
  | zero => simp [denote, eval, FoxRowNormalForm.toHom_apply]
  | term c g => simp [denote, eval, FoxRowNormalForm.toHom_apply, apply_ite, ite_apply]
  | add a b ha hb =>
    simp only [eval, denote, FoxRowNormalForm.toHom_apply,
      FoxCoeff.eval_add_apply, Finset.sum_add_distrib] at ha hb ⊢
    rw [ha, hb]

/-- Proof-free projection of an ORIGINAL certificate's literal operation data. -/
structure Signature (n : ℕ) where
  rowOps : List (FoxRowOp (TameSym n))
  colOps : List (FoxColOp (Generator n) (TameSym n))
  target : FoxNormalForm (Generator n) (TameSym n)

def Signature.ofCertificate {n : ℕ} {A : Type*} [AddCommGroup A]
    {rho : TameSym n → AddMonoid.End A} {M : (Generator n → A) →+ A × A}
    (cert : FoxCertificate rho M) : Signature n :=
  ⟨cert.rowOps, cert.colOps, cert.target⟩

structure Profile (n : ℕ) where
  rowOps : List (RowOp n)
  colOps : List (ColOp n)
  first : PivotRow n
  second : PivotRow n
  inputFirst : LinearRow n
  inputSecond : LinearRow n
  deriving Repr, DecidableEq

def Profile.denote {n : ℕ} (q k : ℕ) (p : Profile n) : Signature n :=
  ⟨p.rowOps.map (RowOp.denote q k), p.colOps.map (ColOp.denote q k),
    ⟨p.first.denote, p.second.denote⟩⟩

def Profile.inputMatrix {n : ℕ} (q k : ℕ) (p : Profile n) :
    FoxNormalForm (Generator n) (TameSym n) :=
  ⟨p.inputFirst.denote q k, p.inputSecond.denote q k⟩

def scalar (n : ℕ) : Profile n :=
  ⟨[.addSnd (.neg .one)], [], .single .tau, .zero,
    .term .one .tau, .term .one .tau⟩

def unramified {n : ℕ} (pivot : Fin (n+1)) : Profile n :=
  ⟨[.scaleFst (.atom (.gen .sigma 1)) (.atom (.gen .sigma (-1))),
    .addSnd (.neg .one),
    .scaleSnd (.oddSum .sigma (-1)) (.add .one (.neg (.atom (.gen .sigma (-1)))))],
   [], .single .tau, .single (.wild pivot),
   .term (.atom (.gen .sigma (-1))) .tau,
   .add (.term .one .tau)
     (.term (.add .one (.neg (.atom (.gen .sigma (-1))))) (.wild pivot))⟩

def sigmaPivot (n : ℕ) : Coeff n :=
  .comp (.atom (.gen .sigma (-1))) (.add (.atom (.gen .tau 1)) (.neg .one))

def sigmaInverse (n : ℕ) : Coeff n :=
  .comp (.oddSum .tau 1) (.atom (.gen .sigma 1))

def tauColumn (n : ℕ) : Coeff n :=
  .add (.atom (.gen .sigma (-1))) (.neg (.normSum .tau))

def ramified {n : ℕ} (pivot : Fin (n+1)) : Profile n :=
  ⟨[.scaleFst (sigmaInverse n) (sigmaPivot n),
    .scaleSnd (.neg (.atom (.gen .sigma 1))) (.neg (.atom (.gen .sigma (-1))))],
   [.transvect .sigma .tau (.neg (.comp (sigmaInverse n) (tauColumn n)))],
   .single .sigma, .single (.wild pivot),
   .add (.term (sigmaPivot n) .sigma) (.term (tauColumn n) .tau),
   .term (.neg (.atom (.gen .sigma (-1)))) (.wild pivot)⟩

theorem denote_scalar (n q k : ℕ) :
    (scalar n).denote q k =
      ⟨[.addSnd (.neg .one)], [], ⟨.single .tau, ⟨fun _ => .zero⟩⟩⟩ := rfl

theorem denote_unramified {n : ℕ} (pivot : Fin (n+1)) (q k : ℕ) :
    (unramified pivot).denote q k =
      ⟨unramIdentityOps n k, [], ⟨.single .tau, .single (.wild pivot)⟩⟩ := rfl

theorem denote_ramified {n : ℕ} (pivot : Fin (n+1)) (q k : ℕ) :
    (ramified pivot).denote q k =
      ⟨ramifiedIdentityRowOps n k, ramifiedIdentityColOps n q k,
        ⟨.single .sigma, .single (.wild pivot)⟩⟩ := rfl

theorem scalar_input_apply {n : ℕ} {C A : Type} [Group C] [AddCommGroup A]
    [DistribMulAction C A] (t : Marking n C) (q k : ℕ) (x : Generator n → A) :
    ((scalar n).inputMatrix q k).toHom (TameSym.splitEnd t) x = (x .tau, x .tau) := by
  change (((scalar n).inputFirst.denote q k).toHom (TameSym.splitEnd t) x,
    ((scalar n).inputSecond.denote q k).toHom (TameSym.splitEnd t) x) = _
  simp only [LinearRow.denote_toHom_apply]
  simp [scalar, LinearRow.eval, Coeff.denote]

theorem unramified_input_apply {n : ℕ} {C A : Type} [Group C] [AddCommGroup A]
    [DistribMulAction C A] (t : Marking n C) (pivot : Fin (n+1)) (q k : ℕ)
    (x : Generator n → A) :
    ((unramified pivot).inputMatrix q k).toHom (TameSym.splitEnd t) x =
      (t.σ⁻¹ • x .tau, x .tau+(x (.wild pivot)-t.σ⁻¹ • x (.wild pivot))) := by
  change (((unramified pivot).inputFirst.denote q k).toHom (TameSym.splitEnd t) x,
    ((unramified pivot).inputSecond.denote q k).toHom (TameSym.splitEnd t) x) = _
  simp only [LinearRow.denote_toHom_apply]
  simp [unramified,
    LinearRow.eval, Coeff.denote,
    TameSym.splitEnd, sub_eq_add_neg]

theorem ramified_input_apply {n : ℕ} {C A : Type} [Group C] [AddCommGroup A]
    [DistribMulAction C A] (t : Marking n C) (pivot : Fin (n+1)) (q k : ℕ)
    (x : Generator n → A) :
    ((ramified pivot).inputMatrix q k).toHom (TameSym.ramifiedEnd t) x =
      (t.σ⁻¹ • (t.τ • x .sigma-x .sigma) +
          (t.σ⁻¹ • x .tau - ∑ i ∈ Finset.range q, t.τ^i • x .tau),
        -(t.σ⁻¹ • x (.wild pivot))) := by
  change (((ramified pivot).inputFirst.denote q k).toHom (TameSym.ramifiedEnd t) x,
    ((ramified pivot).inputSecond.denote q k).toHom (TameSym.ramifiedEnd t) x) = _
  simp only [LinearRow.denote_toHom_apply]
  simp [ramified,
    LinearRow.eval, Coeff.denote,
    sigmaPivot, tauColumn, normPowerCoeff_eval, TameSym.ramifiedEnd, sub_eq_add_neg]

#print axioms Coeff.denote
#print axioms RowOp.denote
#print axioms ColOp.denote
#print axioms PivotRow.denote
#print axioms LinearRow.denote
#print axioms LinearRow.eval
#print axioms LinearRow.denote_toHom_apply
#print axioms Signature.ofCertificate
#print axioms Profile.denote
#print axioms Profile.inputMatrix
#print axioms scalar
#print axioms unramified
#print axioms sigmaPivot
#print axioms sigmaInverse
#print axioms tauColumn
#print axioms ramified
#print axioms denote_scalar
#print axioms denote_unramified
#print axioms denote_ramified
#print axioms scalar_input_apply
#print axioms unramified_input_apply
#print axioms ramified_input_apply

end GQ2.Dyadic.GeneralFoxTemplate
