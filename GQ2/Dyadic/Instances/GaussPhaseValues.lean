/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, and OpenAI Codex
-/
import GQ2.Dyadic.Instances.LHessianCertificates
import GQ2.Dyadic.Instances.WordPhase

/-!
# The Gauss sign and exponent of the wall-handle endpoints, as standalone theorems

The normal-form item of the general-`L_n` certificate displays, for each sector, the signed
Gauss value of the wall-handle endpoint: a sign and a power of two.  Until now the two `L`
values existed only as a `have` inside `LHessianCertificates.unramifiedHessian` and
`.ramifiedHessian`, so nothing outside those two proofs could cite them.

This module names them.  Nothing here is extracted by editing the two proofs: the two `L`
theorems are re-proved from the same producers those proofs use
(`sourceWordPhaseComparison_of_lSqUnramifiedHead`, `lSqUnramifiedPhaseModel_of_headData`,
`ramifiedHeadComparison`, `lSqRamifiedPhaseModel_of_headData`, and the transport lemma
`LHessianCertificates.gauss_eq_of_same_source`), at the same parameters, with the same
`headOperator`.

The compact sectors are a different story and are recorded here rather than re-derived: the
compact wall-handle endpoint value is *already* a standalone theorem, as
`Instances.WordPhase.wPh_compactWallHandlePhase_gaussSum_standardRam` and its `Unram` twin,
with the form-level statement `Certificates.nCompact_handle_form_gaussSum` underneath and the
compact-`M` spelling `wPcM_compactWallHandlePhase_gaussSum` on top.  What was missing there is
only the *display shape*: those theorems land on `(standardNumerics n).gaussRam m`, which
carries the sign implicitly inside a `SourceNumerics` field, not as the separate sign and
exponent the normal-form display prints.  `gaussValCompactDisplay` supplies that shape.

## The display cell

`GaussValCell` is the pair the display prints: a sign in `ℤ` and a degree `n`, the exponent of
two being `m * n` at coefficient rank `2 ^ (2 * m)`.  Its two fields are literals of the three
cell constants, so a driver binds the printed sign and the printed exponent by `rfl`
(`record_target` strength), and binds the equation itself by restating it through the cell
(`restated_identity`).
-/

namespace GQ2.Dyadic.Instances.GaussPhaseValues
noncomputable section
open GQ2 GQ2.SectionEight GQ2.FoxH GQ2.QuadraticFp2
open SectionSeven AffineTLift CentralObstruction ContCoh
open GQ2.Dyadic GQ2.Dyadic.Count GQ2.Dyadic.LSquare
open GQ2.Dyadic.Words GQ2.Dyadic.Words.LSq
open GQ2.Dyadic.Certificates
open Instances.WordPhaseOddCertificates Instances.LPhaseAdditiveNormal
open Instances.LHessianCertificates

/-! ## The display cell -/

/-- The two numbers the normal-form display prints for a Gauss cell: a sign, and the degree
`n` whose product with the coefficient rank `m` is the exponent of two. -/
structure GaussValCell where
  /-- The Gauss sign, `-1` or `+1`. -/
  sign : ℤ
  /-- The degree of the word; the exponent of two is `m * degree`. -/
  degree : ℕ

/-- The integer a cell displays at coefficient rank `2 ^ (2 * m)`. -/
def GaussValCell.value (c : GaussValCell) (m : ℕ) : ℤ := c.sign * 2 ^ (m * c.degree)

/-- The `L` unramified cell: sign `-1` at degree `2 * h + 1`. -/
def gaussValLUnramCell (h : ℕ) : GaussValCell := ⟨-1, 2 * h + 1⟩

/-- The `L` ramified cell: sign `+1` at degree `2 * h + 1`. -/
def gaussValLRamCell (h : ℕ) : GaussValCell := ⟨1, 2 * h + 1⟩

/-- The compact cell, shared by the compact-`N` and compact-`M` sectors: sign `+1` at the even
degree `2 * h + 2`.  There is one compact cell and not two because at even degree the
unramified and ramified targets are the same integer
(`Instances.WordPhase.wPh_gaussUnram_eq_gaussRam_of_even`). -/
def gaussValCompactCell (h : ℕ) : GaussValCell := ⟨1, 2 * h + 2⟩

@[simp] theorem gaussValLUnramCell_sign (h : ℕ) : (gaussValLUnramCell h).sign = -1 := rfl

@[simp] theorem gaussValLUnramCell_degree (h : ℕ) :
    (gaussValLUnramCell h).degree = 2 * h + 1 := rfl

@[simp] theorem gaussValLRamCell_sign (h : ℕ) : (gaussValLRamCell h).sign = 1 := rfl

@[simp] theorem gaussValLRamCell_degree (h : ℕ) :
    (gaussValLRamCell h).degree = 2 * h + 1 := rfl

@[simp] theorem gaussValCompactCell_sign (h : ℕ) : (gaussValCompactCell h).sign = 1 := rfl

@[simp] theorem gaussValCompactCell_degree (h : ℕ) :
    (gaussValCompactCell h).degree = 2 * h + 2 := rfl

/-! ## T1. The `L` sector -/

section L

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
/-- **The unramified `L` endpoint Gauss value, in the `SourceNumerics` spelling.**  This is the
`have hwhole` of `LHessianCertificates.unramifiedHessian` before its final arithmetic step,
re-proved from the same two producers at the same parameters and named. -/
theorem gaussValLUnramifiedStandard
    (hsimple : IsSimpleModTwo (gamma h q : Type) DD.Vmod)
    (hqe : Even q) (m : ℕ) (hm1 : 1 ≤ m) (hcard : Nat.card DD.Vmod = 2 ^ (2 * m))
    (G : LUnramifiedHeadData (DD := DD) rho pi) :
    QuadraticFp2.gaussSum (lSqWallHandlePhase DD.qbar (headOperator rho pi) h)
      = (standardNumerics (2 * h + 1)).gaussUnram m := by
  have C := sourceWordPhaseComparison_of_lSqUnramifiedHead rho base hbase pi hpi hf hm
    hcompat (Vmod_exp2 DD) G.wildTwo hqe G.tau_head G.wild_head G.sigma_fixedPointFree
  obtain ⟨W, instW, Q, ⟨C'⟩, hG⟩ := lSqUnramifiedPhaseModel_of_headData
    rho base hbase pi hpi hf hm hcompat (Vmod_exp2 DD) hsimple hqe m hm1 hcard G
  letI := instW
  dsimp only [headOperator]
  rw [gauss_eq_of_same_source C C', hG]

include base hbase hpi hf hm hcompat in
/-- **The unramified `L` endpoint Gauss value, in the shape the normal-form display prints**:
sign `-1`, exponent `m * (2 * h + 1)`.  This is verbatim the `have hwhole` of
`LHessianCertificates.unramifiedHessian`. -/
theorem gaussValLUnramifiedDisplay
    (hsimple : IsSimpleModTwo (gamma h q : Type) DD.Vmod)
    (hqe : Even q) (m : ℕ) (hm1 : 1 ≤ m) (hcard : Nat.card DD.Vmod = 2 ^ (2 * m))
    (G : LUnramifiedHeadData (DD := DD) rho pi) :
    QuadraticFp2.gaussSum (lSqWallHandlePhase DD.qbar (headOperator rho pi) h)
      = (-1 : ℤ) * 2 ^ (m * (2 * h + 1)) := by
  rw [gaussValLUnramifiedStandard rho base hbase pi hpi hf hm hcompat hsimple hqe m hm1
    hcard G]
  change (-1 : ℤ) ^ (2 * h + 1) * 2 ^ ((2 * h + 1) * m) = (-1) * 2 ^ (m * (2 * h + 1))
  rw [Odd.neg_one_pow (odd_two_mul_add_one h), Nat.mul_comm (2 * h + 1) m]

include base hbase hpi hf hm hcompat in
/-- **The unramified `L` endpoint Gauss value, bound to its display cell.**  The cell's two
fields are the printed sign and the printed degree by `rfl`. -/
theorem gaussValLUnramifiedCell
    (hsimple : IsSimpleModTwo (gamma h q : Type) DD.Vmod)
    (hqe : Even q) (m : ℕ) (hm1 : 1 ≤ m) (hcard : Nat.card DD.Vmod = 2 ^ (2 * m))
    (G : LUnramifiedHeadData (DD := DD) rho pi) :
    QuadraticFp2.gaussSum (lSqWallHandlePhase DD.qbar (headOperator rho pi) h)
      = (gaussValLUnramCell h).value m :=
  gaussValLUnramifiedDisplay rho base hbase pi hpi hf hm hcompat hsimple hqe m hm1 hcard G

include base hbase hpi hf hm hcompat in
/-- **The ramified `L` endpoint Gauss value, in the `SourceNumerics` spelling.**  This is the
`have hwhole` of `LHessianCertificates.ramifiedHessian` before its final arithmetic step,
re-proved from the same two producers at the same parameters and named. -/
theorem gaussValLRamifiedStandard [Finite Cbar]
    (hqe : Even q) (m : ℕ) (hcard : Nat.card DD.Vmod = 2 ^ (2 * m))
    (G : LRamifiedHeadData (DD := DD) rho pi)
    (S : LRamifiedSourceArfData rho (scalarActionZmodTwo_triv _) hcompat) :
    QuadraticFp2.gaussSum (lSqWallHandlePhase DD.qbar (headOperator rho pi) h)
      = (standardNumerics (2 * h + 1)).gaussRam m := by
  have C := ramifiedHeadComparison rho base hbase pi hpi hf hm hcompat hqe G.wild_head
    G.tau_fixedPointFree G.tau_oddPart_fixed
  obtain ⟨W, instW, Q, ⟨C'⟩, hG⟩ := lSqRamifiedPhaseModel_of_headData
    rho base hbase pi hpi hf hm hcompat (Vmod_exp2 DD) hqe m hcard G S
  letI := instW
  dsimp only [headOperator]
  rw [gauss_eq_of_same_source C C', hG]

include base hbase hpi hf hm hcompat in
/-- **The ramified `L` endpoint Gauss value, in the shape the normal-form display prints**:
sign `+1`, exponent `m * (2 * h + 1)`.  This is verbatim the `have hwhole` of
`LHessianCertificates.ramifiedHessian`. -/
theorem gaussValLRamifiedDisplay [Finite Cbar]
    (hqe : Even q) (m : ℕ) (hcard : Nat.card DD.Vmod = 2 ^ (2 * m))
    (G : LRamifiedHeadData (DD := DD) rho pi)
    (S : LRamifiedSourceArfData rho (scalarActionZmodTwo_triv _) hcompat) :
    QuadraticFp2.gaussSum (lSqWallHandlePhase DD.qbar (headOperator rho pi) h)
      = (1 : ℤ) * 2 ^ (m * (2 * h + 1)) := by
  rw [gaussValLRamifiedStandard rho base hbase pi hpi hf hm hcompat hqe m hcard G S]
  change (2 : ℤ) ^ ((2 * h + 1) * m) = 1 * 2 ^ (m * (2 * h + 1))
  rw [one_mul, Nat.mul_comm (2 * h + 1) m]

include base hbase hpi hf hm hcompat in
/-- **The ramified `L` endpoint Gauss value, bound to its display cell.** -/
theorem gaussValLRamifiedCell [Finite Cbar]
    (hqe : Even q) (m : ℕ) (hcard : Nat.card DD.Vmod = 2 ^ (2 * m))
    (G : LRamifiedHeadData (DD := DD) rho pi)
    (S : LRamifiedSourceArfData rho (scalarActionZmodTwo_triv _) hcompat) :
    QuadraticFp2.gaussSum (lSqWallHandlePhase DD.qbar (headOperator rho pi) h)
      = (gaussValLRamCell h).value m :=
  gaussValLRamifiedDisplay rho base hbase pi hpi hf hm hcompat hqe m hcard G S

end L

/-! ## T2. The compact sectors -/

section Compact

open Instances.WordPhase

variable {V : Type} [AddCommGroup V] [Fintype V] {q : V → ZMod 2}

/-- **The compact wall-handle endpoint Gauss value, in the shape the normal-form display
prints**: sign `+1`, exponent `m * (2 * h + 2)`.  The value itself is already a theorem
(`Instances.WordPhase.wPh_compactWallHandlePhase_gaussSum_standardRam`); what is new here is
only the sign-and-exponent shape the display needs. -/
theorem gaussValCompactDisplay (hq : IsQuadraticFp2 q) (hns : Nonsingular q) {m : ℕ}
    (hcard : Fintype.card V = 2 ^ (2 * m)) (h : ℕ) :
    QuadraticFp2.gaussSum (wPhCompactWallHandlePhase q h)
      = (1 : ℤ) * 2 ^ (m * (2 * h + 2)) := by
  rw [wPh_compactWallHandlePhase_gaussSum_standardRam hq hns hcard h]
  change (2 : ℤ) ^ ((2 * h + 2) * m) = 1 * 2 ^ (m * (2 * h + 2))
  rw [one_mul, Nat.mul_comm (2 * h + 2) m]

/-- **The compact wall-handle endpoint Gauss value, bound to its display cell.** -/
theorem gaussValCompactCellEq (hq : IsQuadraticFp2 q) (hns : Nonsingular q) {m : ℕ}
    (hcard : Fintype.card V = 2 ^ (2 * m)) (h : ℕ) :
    QuadraticFp2.gaussSum (wPhCompactWallHandlePhase q h)
      = (gaussValCompactCell h).value m :=
  gaussValCompactDisplay hq hns hcard h

/-- The compact display cell serves both compact branches: at even degree the unramified and
the ramified target are the same integer, so the compact-`N` and compact-`M` sectors print the
same sign and the same exponent. -/
theorem gaussValCompactDisplayUnram (hq : IsQuadraticFp2 q) (hns : Nonsingular q) {m : ℕ}
    (hcard : Fintype.card V = 2 ^ (2 * m)) (h : ℕ) :
    QuadraticFp2.gaussSum (wPhCompactWallHandlePhase q h)
      = (standardNumerics (2 * h + 2)).gaussUnram m :=
  wPh_compactWallHandlePhase_gaussSum_standardUnram hq hns hcard h

end Compact

/-! ## Axiom audit -/

#print axioms GaussValCell
#print axioms GaussValCell.mk
#print axioms GaussValCell.sign
#print axioms GaussValCell.degree
#print axioms GaussValCell.value
#print axioms gaussValLUnramCell
#print axioms gaussValLRamCell
#print axioms gaussValCompactCell
#print axioms gaussValLUnramCell_sign
#print axioms gaussValLUnramCell_degree
#print axioms gaussValLRamCell_sign
#print axioms gaussValLRamCell_degree
#print axioms gaussValCompactCell_sign
#print axioms gaussValCompactCell_degree
#print axioms gaussValLUnramifiedStandard
#print axioms gaussValLUnramifiedDisplay
#print axioms gaussValLUnramifiedCell
#print axioms gaussValLRamifiedStandard
#print axioms gaussValLRamifiedDisplay
#print axioms gaussValLRamifiedCell
#print axioms gaussValCompactDisplay
#print axioms gaussValCompactCellEq
#print axioms gaussValCompactDisplayUnram

end
end GQ2.Dyadic.Instances.GaussPhaseValues
