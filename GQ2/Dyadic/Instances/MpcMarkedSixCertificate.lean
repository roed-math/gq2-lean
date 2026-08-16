/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using OpenAI Codex
-/
import GQ2.Dyadic.Instances.MpcMarkedSupply

/-!
# The explicit full-marked class-six certificate

An exact finite `𝔽₂` computation in
`D_M(2,0) / twoCentralSeries (D_M(2,0)) 6` found a full four-slot marked move for the
class-five witness `mpcFvW5`.  This module records the resulting group words and proves every
part of the certificate that follows from the existing tree:

* the head, `B̄`, and `D̄` corrections belong to `mpcSxKill 4`;
* the pivot correction belongs to `mpcMkPivotKill 4`;
* hence the four words form an `MpcMkFullMove 4`;
* the one remaining quotient equality implies concrete full marked supply at `mpcFvW5`.

The equality itself is deliberately only the proposition `MpcMkC6CertificateKill`.  It is not
asserted, axiomatized, or hidden in a structure field.  Proving it in Lean still requires the
missing class-six collection/normal-form calculation.  Thus the module narrows the finite
class-six blocker to one exact statement without importing an off-tree computation as proof.

Declaration prefix `mpcMkC6` (namespace `GQ2.Dyadic.Instances.MpcMkC6`).  No `sorry`, no new
axiom, no `native_decide`, and no heartbeat or recursion override.
-/

namespace GQ2.Dyadic.Instances.MpcMkC6

open GQ2 GQ2.Dyadic GQ2.Dyadic.MarkedCore Multiplicative
open GQ2.Dyadic.Instances.MpcWord GQ2.Dyadic.Instances.MpcBld
open GQ2.Dyadic.Instances.MpcLad GQ2.Dyadic.Instances.MpcFv
open GQ2.Dyadic.Instances.MpcSx GQ2.Dyadic.Instances.MpcMk
open GQ2.Roe.Labute GQ2.Dyadic.SqCore

noncomputable section

private abbrev A : (DM 2 0 : Type) := dmA 2 0
private abbrev B : (DM 2 0 : Type) := dmB 2 0
private abbrev C : (DM 2 0 : Type) := dmC 2 0
private abbrev D : (DM 2 0 : Type) := dmD 2 0

/-! ## 1. The four words -/

/-- The seven-factor head correction in the sparse finite certificate. -/
def mpcMkC6Us : (DM 2 0 : Type) :=
  commP (commP B D) A ^ 2 * commP (B ^ 2) A ^ 2 * commP (commP B C) B ^ 2 *
    commP (commP (commP B D) B) A * commP (commP (commP B C) B) B *
    commP (commP (commP B D) B) B * commP (commP (commP B D) D) B

/-- The five-factor `B̄`-slot correction in the sparse finite certificate. -/
def mpcMkC6Ut : (DM 2 0 : Type) :=
  B ^ 8 * commP (commP B C) B ^ 2 * commP (commP B D) B ^ 2 *
    commP (commP (commP B C) B) B * commP (commP (commP B D) D) B

/-- The two-factor pivot correction in the sparse finite certificate. -/
def mpcMkC6Um : (DM 2 0 : Type) :=
  commP (commP B D) B ^ 2 * commP (commP (commP B D) B) B

/-- The four-factor `D̄`-slot correction in the sparse finite certificate. -/
def mpcMkC6Un : (DM 2 0 : Type) :=
  commP B C ^ 4 * commP (commP B C) B ^ 2 * commP (commP B C) C ^ 2 *
    commP (commP (commP B C) C) B

/-! ## 2. Carrier and depth facts -/

private theorem comm_mem_marked (x y : (DM 2 0 : Type)) : commP x y ∈ mpcSxMarked :=
  Subgroup.subset_closure (Or.inr ⟨x, y, rfl⟩)

private theorem comm_mem_derived (x y : (DM 2 0 : Type)) : commP x y ∈ mpcMkDerived :=
  Subgroup.subset_closure ⟨x, y, rfl⟩

private theorem comm_three (x y z : (DM 2 0 : Type)) :
    commP (commP x y) z ∈ twoCentralSeries (DM 2 0 : Type) 3 :=
  cfour_commP_mem_three (cfour_commP_mem_two x y) z

private theorem sq_comm_three_four (x y z : (DM 2 0 : Type)) :
    commP (commP x y) z ^ 2 ∈ twoCentralSeries (DM 2 0 : Type) 4 :=
  sq_mem_twoCentralSeries_succ _ (comm_three x y z)

private theorem comm_four (x y z w : (DM 2 0 : Type)) :
    commP (commP (commP x y) z) w ∈ twoCentralSeries (DM 2 0 : Type) 4 :=
  cfour_commP_mem_four (comm_three x y z) w

private theorem sq_comm_sq_four (x y : (DM 2 0 : Type)) :
    commP (x ^ 2) y ^ 2 ∈ twoCentralSeries (DM 2 0 : Type) 4 := by
  apply sq_mem_twoCentralSeries_succ
  apply cfour_commP_mem_three
  exact sq_mem_twoCentralSeries_succ _
    (show x ∈ twoCentralSeries (DM 2 0 : Type) 1 by simp)

private theorem comm_pow_four_mem_four (x y : (DM 2 0 : Type)) :
    commP x y ^ 4 ∈ twoCentralSeries (DM 2 0 : Type) 4 := by
  have h3 : commP x y ^ 2 ∈ twoCentralSeries (DM 2 0 : Type) 3 :=
    sq_mem_twoCentralSeries_succ _ (cfour_commP_mem_two x y)
  have h4 : (commP x y ^ 2) ^ 2 ∈ twoCentralSeries (DM 2 0 : Type) 4 :=
    sq_mem_twoCentralSeries_succ _ h3
  convert h4 using 1
  norm_num [← pow_mul]

/-- The explicit head word is a marked correction four layers down. -/
theorem mpcMkC6Us_mem : mpcMkC6Us ∈ mpcSxKill 4 := by
  refine ⟨?_, ?_⟩
  · simp only [mpcMkC6Us]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _
      (Subgroup.mul_mem _ (Subgroup.mul_mem _
        (Subgroup.pow_mem _ (comm_mem_marked _ _) 2)
        (Subgroup.pow_mem _ (comm_mem_marked _ _) 2))
        (Subgroup.pow_mem _ (comm_mem_marked _ _) 2))
        (comm_mem_marked _ _)) (comm_mem_marked _ _))
        (comm_mem_marked _ _)) (comm_mem_marked _ _)
  · simp only [mpcMkC6Us]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _
      (Subgroup.mul_mem _ (Subgroup.mul_mem _ (sq_comm_three_four B D A)
        (sq_comm_sq_four B A)) (sq_comm_three_four B C B))
        (comm_four B D B A)) (comm_four B C B B))
        (comm_four B D B B)) (comm_four B D D B)

/-- The explicit `B̄`-slot word is a marked correction four layers down. -/
theorem mpcMkC6Ut_mem : mpcMkC6Ut ∈ mpcSxKill 4 := by
  refine ⟨?_, ?_⟩
  · simp only [mpcMkC6Ut]
    have hB8 : B ^ 8 ∈ mpcSxMarked := by
      have h := (mpcSx_pow_mem_kill 2).1
      norm_num at h ⊢
      exact h
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _
      (Subgroup.mul_mem _ hB8 (Subgroup.pow_mem _ (comm_mem_marked _ _) 2))
      (Subgroup.pow_mem _ (comm_mem_marked _ _) 2)) (comm_mem_marked _ _))
      (comm_mem_marked _ _)
  · simp only [mpcMkC6Ut]
    have hB8 : B ^ 8 ∈ twoCentralSeries (DM 2 0 : Type) 4 := by
      have h := (mpcSx_pow_mem_kill 2).2
      norm_num at h ⊢
      exact h
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _
      (Subgroup.mul_mem _ hB8 (sq_comm_three_four B C B))
      (sq_comm_three_four B D B)) (comm_four B C B B)) (comm_four B D D B)

/-- The explicit pivot word is commutator-generated and four layers down. -/
theorem mpcMkC6Um_mem : mpcMkC6Um ∈ mpcMkPivotKill 4 := by
  refine ⟨?_, ?_⟩
  · simp only [mpcMkC6Um]
    exact Subgroup.mul_mem _ (Subgroup.pow_mem _ (comm_mem_derived _ _) 2)
      (comm_mem_derived _ _)
  · simp only [mpcMkC6Um]
    exact Subgroup.mul_mem _ (sq_comm_three_four B D B) (comm_four B D B B)

/-- The explicit `D̄`-slot word is a marked correction four layers down. -/
theorem mpcMkC6Un_mem : mpcMkC6Un ∈ mpcSxKill 4 := by
  refine ⟨?_, ?_⟩
  · simp only [mpcMkC6Un]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _
      (Subgroup.pow_mem _ (comm_mem_marked _ _) 4)
      (Subgroup.pow_mem _ (comm_mem_marked _ _) 2))
      (Subgroup.pow_mem _ (comm_mem_marked _ _) 2)) (comm_mem_marked _ _)
  · simp only [mpcMkC6Un]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _
      (comm_pow_four_mem_four B C) (sq_comm_three_four B C B))
      (sq_comm_three_four B C C)) (comm_four B C C B)

/-- All four explicit words form a legal full marked move at `j = 4`. -/
theorem mpcMkC6_fullMove : MpcMkFullMove 4 mpcMkC6Us mpcMkC6Ut mpcMkC6Um mpcMkC6Un :=
  ⟨mpcMkC6Us_mem, mpcMkC6Ut_mem, mpcMkC6Um_mem, mpcMkC6Un_mem⟩

/-! ## 3. The exact remaining equality -/

/-- The single unproved class-six calculation left by the explicit certificate.  It says
exactly that the W5 defect times the certified full marked increment is trivial in `Q₆`.
This is a definition of a proposition, not an assertion or an axiom. -/
def MpcMkC6CertificateKill : Prop :=
  levelMk (DM 2 0 : Type) 6
    (mpcLadDefect mpcFvW5 *
      mpcBldIncr mpcFvW5.2.1 mpcFvW5.2.2.2 mpcMkC6Us mpcMkC6Ut mpcMkC6Um mpcMkC6Un) = 1

/-- The exact certificate equality would give full marked supply at the concrete W5 point. -/
theorem mpcMkC6_fullSupply_of_certificateKill (h : MpcMkC6CertificateKill) :
    MpcMkFullSupply 4 mpcFvW5 := by
  refine ⟨mpcMkC6Us, mpcMkC6Ut, mpcMkC6Um, mpcMkC6Un, mpcMkC6_fullMove, ?_⟩
  exact (lim_mem_twoCentralSeries_iff_levelMk 6 _).mpr h

/-- The certificate equality in the exact existential shape needed for the `j = 4` rung. -/
theorem mpcMkC6_exists_fullSupply_of_certificateKill (h : MpcMkC6CertificateKill) :
    ∃ p ∈ mpcWordSet 5, MpcMkFullSupply 4 p :=
  ⟨mpcFvW5, mpcFv_w5_mem, mpcMkC6_fullSupply_of_certificateKill h⟩

/-! ## 4. Axiom pins -/

#print axioms mpcMkC6Us
#print axioms mpcMkC6Ut
#print axioms mpcMkC6Um
#print axioms mpcMkC6Un
#print axioms mpcMkC6Us_mem
#print axioms mpcMkC6Ut_mem
#print axioms mpcMkC6Um_mem
#print axioms mpcMkC6Un_mem
#print axioms mpcMkC6_fullMove
#print axioms MpcMkC6CertificateKill
#print axioms mpcMkC6_fullSupply_of_certificateKill
#print axioms mpcMkC6_exists_fullSupply_of_certificateKill

end

end GQ2.Dyadic.Instances.MpcMkC6
