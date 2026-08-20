/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, and OpenAI Codex
-/
import GQ2.Dyadic.Instances.TameInertiaProcyclic

/-!
# Prime-to-two exponents for tame-inertia correction

For even residue cardinality, every finite image of tame inertia has odd order.  Hence every
tame-inertia value is killed by `omega2`.  Removing the maximal pro-`2` component from a
profinite exponent therefore leaves its `tqTau`-power unchanged.

The resulting exponent is the right input for a Stokes-compatible tame correction: its image
in the maximal pro-`2` quotient of `Zhat` is trivial.  The construction is uniform in the word,
rank, handle count, and finite target.
-/

namespace GQ2.Dyadic

noncomputable section

open GQ2
open GQ2.Dyadic.Count

private theorem odd_of_dvd {a b : ℕ} (hab : a ∣ b) (hb : Odd b) : Odd a := by
  obtain ⟨k, rfl⟩ := hab
  exact (Nat.odd_mul.mp hb).1

/-- Every tame-inertia value is killed by the prime-to-odd projector `omega2`. -/
theorem zpowHat_omega2_eq_one_of_mem_inertiaPartQ
    {q : ℕ} (hq0 : q ≠ 0) (hqe : Even q) {x : Tq q}
    (hx : x ∈ inertiaPartQ q) : x ^ᶻ omega2 = 1 := by
  obtain ⟨z, rfl⟩ := exists_zpowHat_tqTau_of_mem_inertiaPartQ hx
  apply eq_one_of_forall_mem_openNormalSubgroup
  intro U
  let mk : ContinuousMonoidHom (Tq q) (Tq q ⧸ U.toSubgroup) :=
    ⟨QuotientGroup.mk' U.toSubgroup, QuotientGroup.continuous_mk⟩
  have hmem : mk ((tqTau q) ^ᶻ z) ∈ Subgroup.zpowers (mk (tqTau q)) := by
    rw [map_zpowHat]
    let a := mk (tqTau q)
    have hopen : IsOpen ((a ^ᶻ ·) ⁻¹' {a ^ᶻ z}) :=
      (continuous_zpowHat a).isOpen_preimage _ (isOpen_discrete _)
    have hzmem : z ∈ (a ^ᶻ ·) ⁻¹' {a ^ᶻ z} := rfl
    let hex := Zhat.denseRange_ofInt.exists_mem_open hopen ⟨z, hzmem⟩
    let n := Classical.choose hex
    have hwn : a ^ᶻ Zhat.ofInt n = a ^ᶻ z := Classical.choose_spec hex
    rw [zpowHat_ofInt] at hwn
    exact Subgroup.mem_zpowers_iff.mpr ⟨n, hwn⟩
  have hyodd : Odd (orderOf (mk ((tqTau q) ^ᶻ z))) := by
    apply odd_of_dvd (Subgroup.orderOf_dvd_natCard _ hmem)
    rw [Nat.card_zpowers]
    exact tqTau_odd_order_map hq0 hqe mk.toMonoidHom
  apply (QuotientGroup.eq_one_iff _).mp
  change mk (((tqTau q) ^ᶻ z) ^ᶻ omega2) = 1
  rw [map_zpowHat]
  exact zpowHat_omega2_eq_one_of_odd hyodd

/-- Remove the maximal pro-`2` component of a profinite exponent. -/
noncomputable def primeToTwoExponent (z : Zhat) : Zhat :=
  z * (z ^ᶻ omega2)⁻¹

/-- Removing the pro-`2` component does not change a power already killed by `omega2`. -/
theorem zpowHat_primeToTwoExponent_of_omega2_eq_one
    {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
    (x : G) (z : Zhat) (hx : (x ^ᶻ z) ^ᶻ omega2 = 1) :
    x ^ᶻ primeToTwoExponent z = x ^ᶻ z := by
  rw [primeToTwoExponent, zpowHat_mul]
  have hmap : x ^ᶻ (z ^ᶻ omega2) = (x ^ᶻ z) ^ᶻ omega2 := by
    let f : ContinuousMonoidHom Zhat G :=
      ⟨{ toFun := (x ^ᶻ ·), map_one' := zpowHat_one x,
         map_mul' := zpowHat_mul x }, continuous_zpowHat x⟩
    exact map_zpowHat f z omega2
  have hinv : x ^ᶻ (z ^ᶻ omega2)⁻¹ = (x ^ᶻ (z ^ᶻ omega2))⁻¹ :=
    map_inv (zpowHatHom x).hom (z ^ᶻ omega2)
  rw [hinv, hmap, hx, inv_one, mul_one]

/-- The corrected exponent has trivial maximal pro-`2` component. -/
theorem maxProPMk_primeToTwoExponent (z : Zhat) :
    maxProPMk 2 Zhat (primeToTwoExponent z) = 1 := by
  rw [primeToTwoExponent, map_mul, map_inv, map_zpowHat]
  rw [zpowHat_omega2_eq_self isProP_maxProPQuotient, mul_inv_cancel]

/-- An exponent with trivial maximal pro-`2` component acts trivially on every pro-`2` group. -/
theorem zpowHat_eq_one_of_maxProPMk_eq_one
    {P : Type} [Group P] [TopologicalSpace P] [IsTopologicalGroup P]
    [CompactSpace P] [T2Space P] [TotallyDisconnectedSpace P]
    (hP : IsProP 2 P) (x : P) {z : Zhat}
    (hz : maxProPMk 2 Zhat z = 1) : x ^ᶻ z = 1 := by
  let f : ContinuousMonoidHom Zhat P :=
    ⟨{ toFun := (x ^ᶻ ·), map_one' := zpowHat_one x,
       map_mul' := zpowHat_mul x }, continuous_zpowHat x⟩
  let fbar : ContinuousMonoidHom (maxProPQuotient 2 Zhat) P :=
    (maxProPHomEquiv hP).symm f
  have hf : fbar.comp (maxProPMk 2 Zhat) = f :=
    (maxProPHomEquiv hP).apply_symm_apply f
  calc
    x ^ᶻ z = f z := rfl
    _ = fbar (maxProPMk 2 Zhat z) := by
      exact (DFunLike.congr_fun hf z).symm
    _ = 1 := by rw [hz, map_one]

/-- Every honest tame-inertia defect has a prime-to-two `tqTau` exponent. -/
theorem exists_primeToTwoExponent_tqTau_of_mem_inertiaPartQ
    {q : ℕ} (hq0 : q ≠ 0) (hqe : Even q) {x : Tq q}
    (hx : x ∈ inertiaPartQ q) :
    ∃ z : Zhat, (tqTau q) ^ᶻ z = x ∧ maxProPMk 2 Zhat z = 1 := by
  obtain ⟨z, hz⟩ := exists_zpowHat_tqTau_of_mem_inertiaPartQ hx
  refine ⟨primeToTwoExponent z, ?_, maxProPMk_primeToTwoExponent z⟩
  rw [zpowHat_primeToTwoExponent_of_omega2_eq_one]
  · exact hz
  · rw [hz]
    exact zpowHat_omega2_eq_one_of_mem_inertiaPartQ hq0 hqe hx

#print axioms zpowHat_omega2_eq_one_of_mem_inertiaPartQ
#print axioms zpowHat_primeToTwoExponent_of_omega2_eq_one
#print axioms maxProPMk_primeToTwoExponent
#print axioms zpowHat_eq_one_of_maxProPMk_eq_one
#print axioms exists_primeToTwoExponent_tqTau_of_mem_inertiaPartQ

end

end GQ2.Dyadic
