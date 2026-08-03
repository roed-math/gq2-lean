/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Codex
-/
import GQ2.Dyadic.Instances.LComparisonSquares
import GQ2.Dyadic.Instances.LSourceComposition

/-!
# The canonical scalar trace orientation for the L source

At scalar coefficients the word differential depends only on the mod-`2` exponent vector of
the resolved words.  Hence all odd L resolvers induce the same scalar differential, even when
only quotient-dependent resolvers are available.  This gives the flexible scalar `H²` map
without asking for a fixed-target scalar resolver.

For the two-relator L family, the `tau` column of the scalar differential is `(1,1)` whenever
`q` is even and `e` is odd.  The sum of the two relator coordinates therefore descends to an
equivalence `WordH² ≃ ZMod 2`.  Composing this trace with the flexible scalar map gives the
canonical source orientation and proves `ScalarTraceCompatible` by construction.
-/

namespace GQ2.Dyadic.LSquare

noncomputable section

open GQ2 GQ2.FoxH GQ2.SectionEight
open ContCoh SectionSeven
open GQ2.Dyadic GQ2.Dyadic.Count GQ2.Dyadic.LiftingDualityG
open GQ2.Dyadic.Words GQ2.Dyadic.Certificates GQ2.Dyadic.Certificates.LSqStokes
open GQ2.Dyadic.Words.LSq GQ2.Dyadic.Certificates.LSq

/-! ## The word trace -/

section WordTrace

variable {iota rel C : Type*} [Fintype iota] [DecidableEq iota] [Fintype rel]
  [Group C] [DistribMulAction C (ZMod 2)]

/-- The sum of relator coordinates, descended to scalar word `H²`. -/
noncomputable def wordH2Trace (c : iota → C) (w : rel → FreeGroup iota)
    (hr : ∀ k, FreeGroup.lift c (w k) = 1) (hend : IsStokesEndpoint w) :
    WordH2 c w (ZMod 2) →+ ZMod 2 :=
  QuotientAddGroup.lift (heisD1 (A := ZMod 2) c w).range
    (AddMonoidHom.mk' (fun v ↦ ∑ k, v k) (fun v v' ↦ by
      simp only [Pi.add_apply, Finset.sum_add_distrib])) (by
        intro v hv
        obtain ⟨x, rfl⟩ := AddMonoidHom.mem_range.mp hv
        exact sum_heisD1_zmod2 hr hend x)

@[simp] theorem wordH2Trace_mk (c : iota → C) (w : rel → FreeGroup iota)
    (hr : ∀ k, FreeGroup.lift c (w k) = 1) (hend : IsStokesEndpoint w)
    (v : rel → ZMod 2) :
    wordH2Trace c w hr hend
      (QuotientAddGroup.mk' (heisD1 (A := ZMod 2) c w).range v) = ∑ k, v k := rfl

end WordTrace

/-! ## Scalar differentials only see mod-2 exponent vectors -/

section ScalarDifferential

variable {iota rel C D : Type*} [Fintype iota] [DecidableEq iota] [Fintype rel]
  [Group C] [DistribMulAction C (ZMod 2)]
  [Group D] [DistribMulAction D (ZMod 2)]

/-- At scalar coefficients the first word differential is the mod-`2` exponent matrix. -/
theorem heisD1_zmod2_apply_eq_eps (c : iota → C) (w : rel → FreeGroup iota)
    (x : iota → ZMod 2) (k : rel) :
    heisD1 (A := ZMod 2) c w x k =
      ∑ i, Multiplicative.toAdd (heisEps i (w k)) * x i := by
  rw [heisD1_apply]
  have aux : ∀ r : FreeGroup iota,
      (FreeGroup.lift (heisGen c x 0) r).a =
        ∑ i, Multiplicative.toAdd (heisEps i r) * x i := by
    intro r
    induction r using FreeGroup.induction_on with
    | C1 => simp [heisEps]
    | of j => simp [FreeGroup.lift_apply_of, heisEps]
    | inv_of r ih =>
        rw [map_inv, HeisLift.inv_a, heisWord_g, ih, smul_zmod2]
        simp only [map_inv, toAdd_inv, neg_mul, Finset.sum_neg_distrib]
    | mul r s ihr ihs =>
        rw [map_mul, HeisLift.mul_a, heisWord_g, smul_zmod2, ihr, ihs]
        simp only [map_mul, toAdd_mul, add_mul, Finset.sum_add_distrib]
  exact aux (w k)

/-- Equal mod-`2` exponent vectors give equal scalar differentials, independently of the base
group and marking. -/
theorem heisD1_zmod2_eq_of_eps
    (c : iota → C) (w : rel → FreeGroup iota)
    (d : iota → D) (v : rel → FreeGroup iota)
    (heps : ∀ k i, heisEps i (w k) = heisEps i (v k)) :
    heisD1 (A := ZMod 2) c w = heisD1 (A := ZMod 2) d v := by
  apply AddMonoidHom.ext
  intro x
  funext k
  rw [heisD1_zmod2_apply_eq_eps, heisD1_zmod2_apply_eq_eps]
  exact Finset.sum_congr rfl fun i _ ↦ congrArg (fun z ↦ Multiplicative.toAdd z * x i) (heps k i)

end ScalarDifferential

/-! ## Odd L resolvers have the same scalar differential -/

section LParity

variable {h q e e' : ℕ}

/-- The tame L word has the same mod-`2` exponent vector at every integer resolver. -/
theorem lSqFam_zero_heisEps_eq
    (i : Generator (2 * h + 1)) :
    heisEps i (lSqFam h q e 0) = heisEps i (lSqFam h q e' 0) := by
  change heisEps i (heisToFree (fun _ ↦ (e : ℤ)) (fun _ ↦ (e : ℤ))
      (tameRelW (2 * h + 1) q)) =
    heisEps i (heisToFree (fun _ ↦ (e' : ℤ)) (fun _ ↦ (e' : ℤ))
      (tameRelW (2 * h + 1) q))
  rw [tameRelW, heisToFree, heisToFree,
    PWord.evalZ_mul, PWord.evalZ_conj, PWord.evalZ_inv, PWord.evalZ_zpow,
    PWord.evalZ_gen, PWord.evalZ_gen, map_mul, map_conjR, conjR_eq_self_of_comm,
    map_inv, map_zpow, PWord.evalZ_mul, PWord.evalZ_conj, PWord.evalZ_inv,
    PWord.evalZ_zpow, PWord.evalZ_gen, PWord.evalZ_gen, map_mul, map_conjR,
    conjR_eq_self_of_comm, map_inv, map_zpow]

/-- The wild L word has the same mod-`2` exponent vector at all odd resolvers. -/
theorem lSqFam_one_heisEps_eq (he : Odd e) (he' : Odd e')
    (i : Generator (2 * h + 1)) :
    heisEps i (lSqFam h q e 1) = heisEps i (lSqFam h q e' 1) := by
  have hform : ∀ n : ℕ,
      heisEps i (lSqFam h q n 1) =
        (heisEps i (FreeGroup.of (coreLetter h 0)))⁻¹ *
          ((heisEps i (FreeGroup.of (coreLetter h 0)) ^ (-3 : ℤ) *
              heisEps i (FreeGroup.of Generator.tau)) ^ (n : ℤ) *
            heisEps i (FreeGroup.of (coreLetter h 1)) ^ (2 : ℤ)) := by
    intro n
    rw [lSqFam_one, heisToFree, evalZ_lSqW]
    simp only [lSqCore, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
    rw [map_mul, heisEps_lSqHandles, mul_one, map_mul, map_mul, map_mul,
      PWord.evalZ_inv, PWord.evalZ_conj, PWord.evalZ_gen, PWord.evalZ_gen, map_inv,
      map_conjR, conjR_eq_self_of_comm, PWord.omega2Pow, PWord.evalZ_profPow, map_zpow,
      PWord.prodList_cons, PWord.prodList_cons, PWord.prodList_nil, PWord.evalZ_mul,
      PWord.evalZ_mul, PWord.evalZ_zpow, PWord.evalZ_gen, PWord.evalZ_gen, PWord.evalZ_one,
      mul_one, map_mul, map_zpow, PWord.evalZ_zpow, PWord.evalZ_gen, map_zpow,
      PWord.evalZ_comm, monoidHom_commR_eq_one, mul_one]
  rw [hform e, hform e']
  have hez : Odd (e : ℤ) := by exact_mod_cast he
  have hez' : Odd (e' : ℤ) := by exact_mod_cast he'
  apply Multiplicative.toAdd.injective
  simp only [toAdd_mul, toAdd_inv, toAdd_zpow]
  rw [zsmul_zmod2_odd hez, zsmul_zmod2_odd hez']

/-- All odd L families have the same mod-`2` exponent matrix. -/
theorem lSqFam_heisEps_eq_of_odd (he : Odd e) (he' : Odd e') :
    ∀ k i, heisEps i (lSqFam h q e k) = heisEps i (lSqFam h q e' k) := by
  intro k i
  fin_cases k
  · exact lSqFam_zero_heisEps_eq i
  · exact lSqFam_one_heisEps_eq he he' i

end LParity

end

end GQ2.Dyadic.LSquare
