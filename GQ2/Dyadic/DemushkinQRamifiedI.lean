/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, and OpenAI Codex
-/
import GQ2.Dyadic.RamifiedI
import GQ2.Dyadic.ProTwoReciprocity
import GQ2.Dyadic.DepthPower
import GQ2.Dyadic.FieldBranchSelector

/-!
# The ramified-`i` reduction of the Demushkin `q`-invariant

For a finite odd-degree dyadic field `K`, this file isolates the exact remaining
local-class-field-theory input needed to prove

`demushkinQ (maxProPQuotient 2 (GalK K)) = 2`.

There is a canonical map from the 2-primary roots of unity in `K` to the torsion of the
topological abelianization of `G_K(2)`, induced by reciprocity.  In odd degree this map is
injective: norm functoriality and the cyclotomic character detect `-1`.  Under ramification of
`K(i)/K`, its source has exactly two elements.  Consequently only surjectivity remains: every
torsion class of `G_K(2)^ab` must be supplied by a 2-primary root of unity in `K`.

That surjectivity is the torsion-only form of the classical local-reciprocity identification
`G_K(2)^ab ≃ (K×)^(2)`.  The current `MarkedRecip` interface gives only a dense reciprocity
map, hence the induced completed map is surjective but not known injective.  The unit-filtration
side has advanced further: `GQ2.Dyadic.DepthPower` proves that the pro-2 completion of the deep
principal units is torsion-free.  What is still absent is the exact completion/decomposition
bridge transferring that result to all of `K×` and identifying the completed reciprocity
kernel.
-/

namespace GQ2.Dyadic

noncomputable section

open GQ2.SectionThree

local notation "ℚbar2" => AlgebraicClosure ℚ_[2]

variable {R : LocalReciprocity}
  {K : IntermediateField ℚ_[2] ℚbar2} [FiniteDimensional ℚ_[2] K]
  [CompactSpace (GalK K)] [TotallyDisconnectedSpace (GalK K)]

/-- The finite-order elements in the topological abelianization of `G_K(2)`, the type whose
cardinality is `demushkinQ (G_K(2))`. -/
abbrev MaxProTwoAbTorsion (K : IntermediateField ℚ_[2] ℚbar2)
    [CompactSpace (GalK K)] [TotallyDisconnectedSpace (GalK K)] :=
  {x : topAbelianization (maxProPQuotient 2 (GalK K)) // IsOfFinOrder x}

/-- A 2-primary root of unity in `K`, viewed as an element of `K×`. -/
def twoPowerRootUnit (x : TwoPowerRoots K) : (↥K)ˣ :=
  Units.mk0 x.1 (by
    intro hx
    obtain ⟨n, hn⟩ := x.2
    rw [hx, zero_pow (pow_ne_zero n two_ne_zero)] at hn
    exact zero_ne_one hn)

@[simp] theorem twoPowerRootUnit_val (x : TwoPowerRoots K) :
    (twoPowerRootUnit x : ↥K) = x.1 := rfl

/-- The canonical reciprocity map from 2-primary roots of unity to torsion in `G_K(2)^ab`. -/
def twoPowerRootToMaxProTwoAbTorsion (B : MarkedRecip R K) :
    TwoPowerRoots K → MaxProTwoAbTorsion K := fun x ↦
  ⟨proTwoReciprocityToTopAb B
      (proPCompletionMk 2 ((↥K)ˣ) (twoPowerRootUnit x)), by
    rw [isOfFinOrder_iff_pow_eq_one]
    obtain ⟨n, hn⟩ := x.2
    refine ⟨2 ^ n, by positivity, ?_⟩
    rw [← map_pow, ← map_pow]
    have hu : twoPowerRootUnit x ^ (2 ^ n) = (1 : (↥K)ˣ) := by
      apply Units.ext
      exact hn
    rw [hu, map_one, map_one]⟩

/-- The cyclotomic character on `G_K(2)`, descended through its topological abelianization. -/
def chiCycKTwoAb :
    ContinuousMonoidHom (topAbelianization (maxProPQuotient 2 (GalK K))) ℤ_[2]ˣ :=
  abLiftG (chiCycKTwo (K := K))

/-- The abelianized maximal-pro-2 cyclotomic character agrees with `chiCycKAb` before the
maximal-pro-2 projection. -/
@[simp] theorem chiCycKTwoAb_topAbToTopAbMaxProP (g : GalKab K) :
    chiCycKTwoAb (K := K) (topAbToTopAbMaxProP (p := 2) (GalK K) g) =
      chiCycKAb K g := by
  obtain ⟨γ, rfl⟩ := surjective_toAbK K g
  change chiCycKTwoAb (K := K)
      (topAbToTopAbMaxProP (p := 2) (GalK K) (abMk γ)) = chiCycK K γ
  rw [topAbToTopAbMaxProP_abMk, chiCycKTwoAb, abLiftG_abMk,
    chiCycKTwo_maxProPMk]

/-- In odd degree the norm of `-1` from `K` to `ℚ₂` is `-1`. -/
theorem normUnitsK_neg_one_of_odd_finrank
    (hodd : Odd (Module.finrank ℚ_[2] K)) :
    normUnitsK K (-1 : (↥K)ˣ) = unitEmbed (-1 : ℤ_[2]ˣ) := by
  apply Units.ext
  rw [normUnitsK_val, unitEmbed_val]
  change Algebra.norm ℚ_[2] (-1 : ↥K) = algebraMap ℤ_[2] ℚ_[2] (-1 : ℤ_[2])
  rw [show (-1 : ↥K) = algebraMap ℚ_[2] ↥K (-1 : ℚ_[2]) by simp,
    Algebra.norm_algebraMap, hodd.neg_one_pow]
  norm_num

/-- Norm functoriality and the `ℚ₂` cyclotomic reciprocity normalization detect the class
of `-1` over every odd-degree `K`. -/
theorem chiCycKAb_recip_neg_one_of_odd_finrank (B : MarkedRecip R K)
    (hodd : Odd (Module.finrank ℚ_[2] K)) :
    chiCycKAb K (B.recip (-1 : (↥K)ˣ)) = (-1 : ℤ_[2]ˣ) := by
  rw [← chiCycAb_inclAbK, B.norm_compat,
    normUnitsK_neg_one_of_odd_finrank hodd, R.chiCyc_recip_unit]
  simp

/-- A root equal to `1` maps to the identity torsion class. -/
theorem twoPowerRootToMaxProTwoAbTorsion_eq_one_of_val_eq_one
    (B : MarkedRecip R K) (x : TwoPowerRoots K) (hx : (x : K) = 1) :
    (twoPowerRootToMaxProTwoAbTorsion B x).1 = 1 := by
  change proTwoReciprocityToTopAb B
      (proPCompletionMk 2 ((↥K)ˣ) (twoPowerRootUnit x)) = 1
  have hu : twoPowerRootUnit x = (1 : (↥K)ˣ) := by
    apply Units.ext
    exact hx
  rw [hu, map_one, map_one]

/-- A root equal to `-1` has cyclotomic value `-1` after reciprocity. -/
theorem chiCycKTwoAb_twoPowerRootToMaxProTwoAbTorsion_eq_neg_one
    (B : MarkedRecip R K) (hodd : Odd (Module.finrank ℚ_[2] K))
    (x : TwoPowerRoots K) (hx : (x : K) = -1) :
    chiCycKTwoAb (K := K) (twoPowerRootToMaxProTwoAbTorsion B x).1 = (-1 : ℤ_[2]ˣ) := by
  change chiCycKTwoAb (K := K)
    (proTwoReciprocityToTopAb B
      (proPCompletionMk 2 ((↥K)ˣ) (twoPowerRootUnit x))) = _
  rw [proTwoReciprocityToTopAb_mk, chiCycKTwoAb_topAbToTopAbMaxProP]
  have hu : twoPowerRootUnit x = (-1 : (↥K)ˣ) := by
    apply Units.ext
    exact hx
  rw [hu, chiCycKAb_recip_neg_one_of_odd_finrank B hodd]

/-- **Odd-degree injectivity.**  Under ramification of `K(i)/K`, the canonical map from the two
2-primary roots `±1` into the torsion of `G_K(2)^ab` does not collapse them. -/
theorem twoPowerRootToMaxProTwoAbTorsion_injective_of_odd_ramifiedI
    (B : MarkedRecip R K) (hodd : Odd (Module.finrank ℚ_[2] K))
    (RI : RamifiedIData K) :
    Function.Injective (twoPowerRootToMaxProTwoAbTorsion B) := by
  intro x y hxy
  apply Subtype.ext
  rcases twoPowerRoot_eq_one_or_neg_one_of_ramifiedI RI.sq_deltaI RI.ramified
      x x.2.choose x.2.choose_spec with hx | hx <;>
    rcases twoPowerRoot_eq_one_or_neg_one_of_ramifiedI RI.sq_deltaI RI.ramified
      y y.2.choose y.2.choose_spec with hy | hy
  · exact hx.trans hy.symm
  · have hchi := congrArg
        (fun z : MaxProTwoAbTorsion K ↦ chiCycKTwoAb (K := K) z.1) hxy
    rw [twoPowerRootToMaxProTwoAbTorsion_eq_one_of_val_eq_one B x hx,
      map_one,
      chiCycKTwoAb_twoPowerRootToMaxProTwoAbTorsion_eq_neg_one B hodd y hy] at hchi
    exact ((by norm_num : (1 : ℤ_[2]ˣ) ≠ -1) hchi).elim
  · have hchi := congrArg
        (fun z : MaxProTwoAbTorsion K ↦ chiCycKTwoAb (K := K) z.1) hxy
    rw [chiCycKTwoAb_twoPowerRootToMaxProTwoAbTorsion_eq_neg_one B hodd x hx,
      twoPowerRootToMaxProTwoAbTorsion_eq_one_of_val_eq_one B y hy,
      map_one] at hchi
    exact ((by norm_num : (-1 : ℤ_[2]ˣ) ≠ 1) hchi).elim
  · exact hx.trans hy.symm

/-- The exact remaining torsion-only local-CFT premise: every finite-order class in
`G_K(2)^ab` is the reciprocity image of a 2-primary root of unity in `K`. -/
def MaxProTwoAbTorsionGeneratedByFieldRoots (B : MarkedRecip R K) : Prop :=
  Function.Surjective (twoPowerRootToMaxProTwoAbTorsion B)

/-- **Ramified-`i`, odd-degree `q = 2` reduction.**  The field theorem follows from the exact
torsion-surjectivity premise above; injectivity and the cardinality-two calculation are proved
in the repository. -/
theorem demushkinQ_maxProTwoGalK_eq_two_of_odd_ramifiedI
    (B : MarkedRecip R K) (hodd : Odd (Module.finrank ℚ_[2] K))
    (RI : RamifiedIData K) (htor : MaxProTwoAbTorsionGeneratedByFieldRoots B) :
    demushkinQ (maxProPQuotient 2 (GalK K)) = 2 := by
  rw [demushkinQ]
  let e : TwoPowerRoots K ≃ MaxProTwoAbTorsion K :=
    Equiv.ofBijective (twoPowerRootToMaxProTwoAbTorsion B)
      ⟨twoPowerRootToMaxProTwoAbTorsion_injective_of_odd_ramifiedI B hodd RI, htor⟩
  rw [← Nat.card_congr e]
  exact natCard_twoPowerRoots_of_ramifiedI RI.sq_deltaI RI.ramified

/-- **Exact reduction.**  For odd-degree `K` with ramified `K(i)/K`, the field-theoretic
`demushkinQ = 2` statement is equivalent to the single torsion-surjectivity premise.  Thus the
premise does not hide any extra size condition: its injectivity half follows from the existing
marked reciprocity normalization and norm functoriality. -/
theorem maxProTwoAbTorsionGeneratedByFieldRoots_iff_demushkinQ_eq_two
    (B : MarkedRecip R K) (hodd : Odd (Module.finrank ℚ_[2] K))
    (RI : RamifiedIData K) :
    MaxProTwoAbTorsionGeneratedByFieldRoots B ↔
      demushkinQ (maxProPQuotient 2 (GalK K)) = 2 := by
  constructor
  · exact demushkinQ_maxProTwoGalK_eq_two_of_odd_ramifiedI B hodd RI
  · intro hq
    have hcardTarget : Nat.card (MaxProTwoAbTorsion K) = 2 := by
      simpa only [demushkinQ] using hq
    letI : Finite (MaxProTwoAbTorsion K) :=
      Nat.finite_of_card_ne_zero (by rw [hcardTarget]; norm_num)
    have hcardSource : Nat.card (TwoPowerRoots K) = 2 :=
      natCard_twoPowerRoots_of_ramifiedI RI.sq_deltaI RI.ramified
    exact ((Nat.bijective_iff_injective_and_card
      (twoPowerRootToMaxProTwoAbTorsion B)).2
        ⟨twoPowerRootToMaxProTwoAbTorsion_injective_of_odd_ramifiedI B hodd RI,
          hcardSource.trans hcardTarget.symm⟩).2

end

end GQ2.Dyadic
