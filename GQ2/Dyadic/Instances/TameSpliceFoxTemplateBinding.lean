/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, and OpenAI Codex
-/
import GQ2.Dyadic.Word.GeneralFoxTemplate

/-!
# STAGED Fox templates bound to actual certified pair/mobile records

All six statements identify the literal row-operation list, column-operation list,
and target of an original FoxCertificate with the symbolic template denotation.
They are definitional equalities, not consequences of operator evaluation. The
actual nontrivial-sector k is the derived action half-period, never an invented
period, rank, or sampled coefficient-space parameter. All source/action hypotheses
of the concrete records are retained in these bindings.
-/

namespace GQ2.Dyadic.GeneralFoxTemplate
noncomputable section
open GQ2 Count Certificates Words MarkedCore
open Instances.TameSpliceFoxCertificates
open Instances.TameSplicePolynomialFoxCertificates
open Instances.TameSpliceRamifiedPolynomialFoxCertificates
open Instances.EvenMHeadHandlePairSpliceSupply Instances.MpcMobileNuSource

variable {alpha h q : ℕ} {C A : Type} [Group C] [Finite C]
  [AddCommGroup A] [Finite A] [DistribMulAction C A]
  (t : Marking (2+2*h) C) (halpha : 1 ≤ alpha) (hq0 : q≠0) (hqe : Even q)
  (nuP : ContinuousMonoidHom (DM alpha h : Type) Ztwo) (hA2 : ∀ a : A, a+a=0)

theorem scalar_pair_signature (j : Fin h)
    (htriv : ∀ (g : Generator (2+2*h)) (a : A), t g • a=a) :
    (scalar (2+2*h)).denote q 0 = Signature.ofCertificate
      (pairSplice_FoxCertificate_scalar t halpha hq0 hqe j nuP hA2 htriv) := rfl

theorem scalar_mobile_signature {r p : ℕ} (eta : ℤ_[2]ˣ)
    (htriv : ∀ (g : Generator (2+2*h)) (a : A), t g • a=a) :
    (scalar (2+2*h)).denote q 0 = Signature.ofCertificate
      (mobileSplice_FoxCertificate_scalar (r := r) (p := p)
        t halpha hq0 hqe eta nuP hA2 htriv) := rfl

section Unramified
variable [TopologicalSpace C] [DiscreteTopology C]
  (hwild : ∀ (i : Fin (2+2*h+1)) (a : A), t.x i • a=a)
  (htau : ∀ a : A, t.τ • a=a)
  (hsigma : ∀ a : A, t.σ • a=a → a=0)
  (hsigma2 : ∀ a : A, powOmega2 t.σ • a=a)

theorem unramified_pair_signature (j : Fin h)
    (hr : ∀ l, FreeGroup.lift ⇑t
      (pinnedResolvedFamily (2+2*h) q (headHandlePairSpliceW alpha h q halpha hq0 hqe j nuP)
        (4*Monoid.exponent C) l)=1) :
    (unramified (x2Idx h)).denote q (sigmaActionHalfPeriod (A := A) t) =
      Signature.ofCertificate (pairSplice_FoxCertificate_unramified_identity
        t halpha hq0 hqe j nuP hA2 hwild htau hsigma hsigma2 hr) := rfl

theorem unramified_mobile_signature {r p : ℕ} (eta : ℤ_[2]ˣ)
    (hr : ∀ l, FreeGroup.lift ⇑t
      (pinnedResolvedFamily (2+2*h) q
        (tameSplice (mpcMobileTameCorrectedW hq0 hqe alpha r p h eta halpha nuP)
          (Words.MCompact.mCompactW alpha h)) (4*Monoid.exponent C) l)=1) :
    (unramified (x2Idx h)).denote q (sigmaActionHalfPeriod (A := A) t) =
      Signature.ofCertificate (mobileSplice_FoxCertificate_unramified_identity
        t halpha hq0 hqe eta nuP hA2 hwild htau hsigma hsigma2 hr) := rfl
end Unramified

section Ramified
variable {D : Type} [Group D] [Finite D] [DistribMulAction D A]
  (pi : C →* D) (hpi : ∀ (c : C) (a : A), c • a=pi c • a)
  (hsurj : Function.Surjective pi) (ht : t.TameRelAt q)
  (hwild : ∀ i, pi (t.x i)=1)
  (hfpf : ∀ a : A, t.τ • a=a → a=0)
  (hodd : ∀ a : A, powOmega2 t.τ • a=a)

theorem ramified_pair_signature (j : Fin h) :
    (ramified (x2Idx h)).denote q (tauActionHalfPeriod (A := A) t) =
      Signature.ofCertificate (pairSplice_FoxCertificate_ramified_identity
        t halpha hq0 hqe j nuP hA2 pi hpi hsurj ht hwild hfpf hodd) := rfl

theorem ramified_mobile_signature {r p : ℕ} (eta : ℤ_[2]ˣ) :
    (ramified (x2Idx h)).denote q (tauActionHalfPeriod (A := A) t) =
      Signature.ofCertificate (mobileSplice_FoxCertificate_ramified_identity
        (r := r) (p := p) t halpha hq0 hqe eta nuP hA2 pi hpi hsurj ht hwild hfpf hodd) := rfl
end Ramified

#print axioms scalar_pair_signature
#print axioms scalar_mobile_signature
#print axioms unramified_pair_signature
#print axioms unramified_mobile_signature
#print axioms ramified_pair_signature
#print axioms ramified_mobile_signature

end
end GQ2.Dyadic.GeneralFoxTemplate
