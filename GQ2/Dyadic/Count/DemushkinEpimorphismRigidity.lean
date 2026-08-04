/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using OpenAI Codex
-/
import GQ2.Demushkin
import GQ2.FrattiniCriterion
import GQ2.Dyadic.Count.H2SylowPreimageDevissage
import GQ2.Dyadic.Count.Scalar
import GQ2.Dyadic.LocalGauss.PairingK
import GQ2.MaxProPCohomology

/-!
# Epimorphism rigidity for pro-two Demushkin groups

This file isolates the low-degree cohomological core of the standard rigidity argument for a
continuous epimorphism between finitely generated pro-`2` Demushkin groups of equal rank.

Degree-one inflation is injective for every surjection.  Equal Demushkin rank therefore makes
it bijective.  Cup-product naturality and nondegeneracy then imply that degree-two inflation is
nonzero, hence bijective because both degree-two groups have order two.

What remains is exactly the kernel term in the continuous Hochschild--Serre five-term sequence:
bijectivity in degree one and injectivity in degree two force the conjugation-invariant
mod-two characters of the kernel to vanish.  The final definitions expose this seam separately
from the pro-two group fact that a nontrivial closed normal subgroup has such a character.
-/

set_option autoImplicit false

namespace GQ2.Dyadic

open GQ2 ContCoh

noncomputable section

section Inflation

variable {G H : Type}
  [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [Group H] [TopologicalSpace H] [IsTopologicalGroup H]

local instance scalarActionKernelG : DistribMulAction G (ZMod 2) := scalarActionZmodTwo G
local instance scalarContinuousKernelG : ContinuousSMul G (ZMod 2) :=
  scalarActionZmodTwo_continuousSMul G
local instance scalarActionKernelH : DistribMulAction H (ZMod 2) := scalarActionZmodTwo H
local instance scalarContinuousKernelH : ContinuousSMul H (ZMod 2) :=
  scalarActionZmodTwo_continuousSMul H

/-- Mod-two degree-one inflation along a continuous homomorphism, with the canonical trivial
scalar actions at source and target. -/
def demushkinH1Inflation (f : ContinuousMonoidHom G H) :
    H1 H (ZMod 2) →+ H1 G (ZMod 2) :=
  inf1 f (fun _ _ ↦ rfl)

/-- Mod-two degree-two inflation along a continuous homomorphism, with the canonical trivial
scalar actions at source and target. -/
def demushkinH2Inflation (f : ContinuousMonoidHom G H) :
    H2 H (ZMod 2) →+ H2 G (ZMod 2) :=
  inf2 f (fun _ _ ↦ rfl)

/-- Degree-one inflation with trivial coefficients is injective along every surjection. -/
theorem demushkinH1Inflation_injective_of_surjective
    (f : ContinuousMonoidHom G H) (hf : Function.Surjective f) :
    Function.Injective (demushkinH1Inflation f) := by
  intro x y hxy
  obtain ⟨zx, rfl⟩ := H1mk_surjective (G := H) (M := ZMod 2) x
  obtain ⟨zy, rfl⟩ := H1mk_surjective (G := H) (M := ZMod 2) y
  rw [demushkinH1Inflation, inf1_H1mk, inf1_H1mk] at hxy
  have hz := congrArg
    (H1equivZ1OfTrivial (G := G) (M := ZMod 2) (scalarActionZmodTwo_triv G)) hxy
  apply congrArg (H1mk H (ZMod 2))
  apply Subtype.ext
  funext h
  obtain ⟨g, rfl⟩ := hf h
  exact congrFun (congrArg Subtype.val hz) g

/-- Inflation commutes with the trivial-coefficient cup product. -/
theorem demushkinH2Inflation_trivialCupPairing
    (f : ContinuousMonoidHom G H) (x y : H1 H (ZMod 2)) :
    demushkinH2Inflation f
        (trivialCupPairing 2 H (scalarActionZmodTwo_triv H) x y) =
      trivialCupPairing 2 G (scalarActionZmodTwo_triv G)
        (demushkinH1Inflation f x) (demushkinH1Inflation f y) := by
  obtain ⟨a, rfl⟩ := H1mk_surjective (G := H) (M := ZMod 2) x
  obtain ⟨b, rfl⟩ := H1mk_surjective (G := H) (M := ZMod 2) y
  simp only [trivialCupPairing, demushkinH1Inflation, demushkinH2Inflation]
  rw [cup11_mk_mk, inf2_H2mk, inf1_H1mk, inf1_H1mk, cup11_mk_mk]
  rfl

/-- A surjection between Demushkin groups of equal rank induces an isomorphism on mod-two
degree-one cohomology. -/
theorem demushkinH1Inflation_bijective_of_surjective_of_rank_eq
    (f : ContinuousMonoidHom G H) (hf : Function.Surjective f)
    (hDG : IsDemushkin 2 G) (hDH : IsDemushkin 2 H)
    (hrank : demushkinRank 2 G = demushkinRank 2 H) :
    Function.Bijective (demushkinH1Inflation f) := by
  letI : Finite (H1 G (ZMod 2)) := hDG.finiteH1
  letI : Finite (H1 H (ZMod 2)) := hDH.finiteH1
  apply (demushkinH1Inflation_injective_of_surjective f hf).bijective_of_nat_card_le
  rw [hDG.card_H1_eq_pow, hDH.card_H1_eq_pow, hrank]

/-- Surjectivity in degree one makes degree-two inflation nonzero between positive-rank
Demushkin groups.  Since both degree-two groups have order two, it is injective. -/
theorem demushkinH2Inflation_injective_of_demushkin_of_H1_surjective
    (f : ContinuousMonoidHom G H)
    (hDG : IsDemushkin 2 G) (hDH : IsDemushkin 2 H)
    (hrank : 0 < demushkinRank 2 G)
    (hH1 : Function.Surjective (demushkinH1Inflation f)) :
    Function.Injective (demushkinH2Inflation f) := by
  letI : Finite (H1 G (ZMod 2)) := hDG.finiteH1
  letI : Fintype (H1 G (ZMod 2)) := Fintype.ofFinite _
  have hH1card : Fintype.card (H1 G (ZMod 2)) = 2 ^ demushkinRank 2 G := by
    rw [← Nat.card_eq_fintype_card]
    exact hDG.card_H1_eq_pow
  have hH1large : 1 < Fintype.card (H1 G (ZMod 2)) := by
    rw [hH1card]
    exact Nat.one_lt_pow hrank.ne' (by omega)
  obtain ⟨a, b, hab⟩ := Fintype.one_lt_card_iff.mp hH1large
  let x := a - b
  have hx : x ≠ 0 := sub_ne_zero.mpr hab
  obtain ⟨y, hxy⟩ := hDG.nondegen_left' (scalarActionZmodTwo_triv G) x hx
  obtain ⟨xH, hxH⟩ := hH1 x
  obtain ⟨yH, hyH⟩ := hH1 y
  let cupH := trivialCupPairing 2 H (scalarActionZmodTwo_triv H) xH yH
  have hcupImage : demushkinH2Inflation f cupH =
      trivialCupPairing 2 G (scalarActionZmodTwo_triv G) x y := by
    dsimp only [cupH]
    rw [demushkinH2Inflation_trivialCupPairing, hxH, hyH]
  obtain ⟨w, hw, hwuniq⟩ :=
    (Nat.card_eq_two_iff' (0 : H2 H (ZMod 2))).mp hDH.cardH2
  have hcupw : cupH = w := by
    apply hwuniq cupH
    intro hzero
    apply hxy
    rw [← hcupImage, hzero, map_zero]
  have hfw : demushkinH2Inflation f w ≠ 0 := by
    rw [← hcupw, hcupImage]
    exact hxy
  apply (injective_iff_map_eq_zero _).mpr
  intro z hz
  by_contra hz0
  have hzw : z = w := hwuniq z hz0
  exact hfw (hzw ▸ hz)

/-- Under the same hypotheses, degree-two inflation is an isomorphism, not merely injective. -/
theorem demushkinH2Inflation_bijective_of_demushkin_of_H1_surjective
    (f : ContinuousMonoidHom G H)
    (hDG : IsDemushkin 2 G) (hDH : IsDemushkin 2 H)
    (hrank : 0 < demushkinRank 2 G)
    (hH1 : Function.Surjective (demushkinH1Inflation f)) :
    Function.Bijective (demushkinH2Inflation f) := by
  letI : Finite (H2 G (ZMod 2)) := Nat.finite_of_card_ne_zero (by
    rw [hDG.cardH2]
    decide)
  apply (demushkinH2Inflation_injective_of_demushkin_of_H1_surjective
    f hDG hDH hrank hH1).bijective_of_nat_card_le
  rw [hDG.cardH2, hDH.cardH2]

end Inflation

/-- A continuous mod-two character of the kernel fixed by ambient conjugation.  These are the
elements of `H¹(ker f, 𝔽₂)^H` in literal character form. -/
def IsInvariantKernelCharacter {G H : Type} [Group G] [TopologicalSpace G]
    [Group H] [TopologicalSpace H] (f : ContinuousMonoidHom G H)
    (chi : ContinuousMonoidHom ↥f.toMonoidHom.ker (Multiplicative (ZMod 2))) : Prop :=
  ∀ (g : G) (n : ↥f.toMonoidHom.ker),
    chi ⟨g * n.1 * g⁻¹, by
      show f (g * n.1 * g⁻¹) = 1
      have hn : f n.1 = 1 := n.2
      rw [map_mul, map_mul, map_inv, hn]
      group⟩ = chi n

section FiniteInvariantCharacter

variable {P Q : Type} [Group P] [Finite P] [Group Q] [Finite Q]

/-- The indicator of an index-two subgroup, in additive character notation. -/
noncomputable def indexTwoAdditiveCharacter (M : Subgroup P) (hM : M.index = 2) :
    Additive P →+ ZMod 2 := by
  classical
  exact
    { toFun := fun x ↦ if Additive.toMul x ∈ M then 0 else 1
      map_zero' := if_pos M.one_mem
      map_add' := by
        intro a b
        change (if Additive.toMul a * Additive.toMul b ∈ M then (0 : ZMod 2) else 1) =
          (if Additive.toMul a ∈ M then 0 else 1) +
            (if Additive.toMul b ∈ M then 0 else 1)
        have hkey := mul_mem_iff_of_index_two hM (Additive.toMul a) (Additive.toMul b)
        by_cases ha : Additive.toMul a ∈ M <;>
          by_cases hb : Additive.toMul b ∈ M <;>
          simp only [hkey, ha, hb, if_true, if_false, iff_true, iff_false, iff_self] <;> decide }

/-- An index-two subgroup produces a nonzero mod-two `H¹` class. -/
theorem nontrivial_H1_zmodTwo_of_indexTwoSubgroup
    [TopologicalSpace P] [DiscreteTopology P]
    [DistribMulAction P (ZMod 2)] [ContinuousSMul P (ZMod 2)]
    (htriv : ∀ (p : P) (x : ZMod 2), p • x = x)
    (M : Subgroup P) (hM : M.index = 2) : Nontrivial (H1 P (ZMod 2)) := by
  classical
  let chi := indexTwoAdditiveCharacter M hM
  let z : Z1 P (ZMod 2) := ⟨fun p ↦ chi (Additive.ofMul p),
    (mem_Z1_iff_of_trivial htriv).mpr ⟨continuous_of_discreteTopology,
      fun _ _ ↦ map_add chi _ _⟩⟩
  have hz : z ≠ 0 := by
    intro hz0
    have hMne : M ≠ ⊤ := by
      intro htop
      have : M.index = 1 := Subgroup.index_eq_one.mpr htop
      omega
    obtain ⟨p, hp⟩ := SetLike.exists_of_lt (lt_top_iff_ne_top.mpr hMne)
    have hpM : p ∉ M := hp.2
    have hzval := congrFun (congrArg Subtype.val hz0) p
    change (if p ∈ M then (0 : ZMod 2) else 1) = 0 at hzval
    rw [if_neg hpM] at hzval
    exact one_ne_zero hzval
  let E := H1equivZ1OfTrivial (G := P) (M := ZMod 2) htriv
  refine ⟨E.symm z, 0, ?_⟩
  intro h
  apply hz
  have h' := congrArg E h
  simpa [E] using h'

/-- A finite `2`-group epimorphism with nontrivial kernel has a nonzero invariant kernel
character.  This is the finite fixed-vector core of the profinite kernel supply. -/
theorem finiteTwoGroup_invariantKernelCharacterSupply
    [TopologicalSpace P] [DiscreteTopology P]
    [TopologicalSpace Q] [DiscreteTopology Q]
    (f : ContinuousMonoidHom P Q) (hf : Function.Surjective f)
    (hP : IsPGroup 2 P) (hne : ∃ n : ↥f.toMonoidHom.ker, n ≠ 1) :
    ∃ chi : ContinuousMonoidHom ↥f.toMonoidHom.ker (Multiplicative (ZMod 2)),
      IsInvariantKernelCharacter f chi ∧ ∃ n, chi n ≠ 1 := by
  let N := f.toMonoidHom.ker
  letI : Finite N := Finite.of_injective N.subtype Subtype.val_injective
  haveI : Nontrivial N := ⟨hne.choose, 1, hne.choose_spec⟩
  have hNP : IsPGroup 2 N := hP.to_subgroup N
  obtain htop | ⟨M, hM, _hbotM⟩ := eq_top_or_exists_le_coatom (⊥ : Subgroup N)
  · exact absurd htop (bot_ne_top : (⊥ : Subgroup N) ≠ ⊤)
  letI : M.Normal := coatom_normal_of_pGroup hNP hM
  have hMindex : M.index = 2 := coatom_index_of_pGroup hNP hM
  letI : DistribMulAction P (ZMod 2) := scalarActionZmodTwo P
  letI : ContinuousSMul P (ZMod 2) := scalarActionZmodTwo_continuousSMul P
  letI : DistribMulAction N (ZMod 2) := scalarActionZmodTwo N
  letI : ContinuousSMul N (ZMod 2) := scalarActionZmodTwo_continuousSMul N
  letI : Nontrivial (H1 N (ZMod 2)) :=
    nontrivial_H1_zmodTwo_of_indexTwoSubgroup (scalarActionZmodTwo_triv N) M hMindex
  letI : DistribMulAction Q (H1 N (ZMod 2)) := conjModule f hf
  letI : Finite (Z1 N (ZMod 2)) := inferInstance
  letI : Finite (H1 N (ZMod 2)) :=
    Finite.of_equiv _
      (H1equivZ1OfTrivial (G := N) (M := ZMod 2) (scalarActionZmodTwo_triv N)).symm.toEquiv
  have hQ : IsPGroup 2 Q := hP.of_surjective f hf
  obtain ⟨xi, hxi, hxifix⟩ := FoxH.exists_ne_zero_fixed_of_isPGroup_two hQ
    (fun x : H1 N (ZMod 2) ↦ by
      simpa only [two_nsmul] using nsmul_H1_eq_zero (p := 2) x)
  let z := H1equivZ1OfTrivial (G := N) (M := ZMod 2) (scalarActionZmodTwo_triv N) xi
  let chi : ContinuousMonoidHom N (Multiplicative (ZMod 2)) := Count.homEquivZ1.symm z
  let E := H1equivZ1OfTrivial (G := N) (M := ZMod 2) (scalarActionZmodTwo_triv N)
  have hE_mk (a : Z1 N (ZMod 2)) : E (H1mk N (ZMod 2) a) = a := by
    apply E.symm.injective
    rw [E.symm_apply_apply]
    rfl
  have hxi_mk : H1mk N (ZMod 2) z = xi := by
    apply E.injective
    rw [hE_mk]
  refine ⟨chi, ?_, ?_⟩
  · intro g n
    have hfix := hxifix (f g⁻¹)
    change conjAct f (Function.surjInv hf (f g⁻¹)) xi = xi at hfix
    have heq := conjAct_ker f (Function.surjInv hf (f g⁻¹)) g⁻¹
      (Function.surjInv_eq hf _) xi
    rw [heq] at hfix
    have hfix_mk : conjAct f g⁻¹ (H1mk N (ZMod 2) z) = H1mk N (ZMod 2) z := by
      rw [hxi_mk]
      exact hfix
    rw [conjAct_H1mk] at hfix_mk
    have hzfix := congrArg E hfix_mk
    rw [hE_mk, hE_mk] at hzfix
    have hzval := congrFun (congrArg Subtype.val hzfix) n
    apply Multiplicative.toAdd.injective
    change z.1 ⟨g * n.1 * g⁻¹, _⟩ = z.1 n
    convert hzval using 1
    apply congrArg z.1
    apply Subtype.ext
    show g * n.1 * g⁻¹ = (g⁻¹)⁻¹ * n.1 * g⁻¹
    group
  · by_contra hzero
    push Not at hzero
    apply hxi
    apply E.injective
    apply Subtype.ext
    funext n
    have hn := hzero n
    change Multiplicative.ofAdd (z.1 n) = 1 at hn
    exact congrArg Multiplicative.toAdd hn

end FiniteInvariantCharacter

section KernelBoundary

variable {G H : Type}
  [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
  [Group H] [TopologicalSpace H] [IsTopologicalGroup H]

local instance scalarActionBoundaryG : DistribMulAction G (ZMod 2) := scalarActionZmodTwo G
local instance scalarContinuousBoundaryG : ContinuousSMul G (ZMod 2) :=
  scalarActionZmodTwo_continuousSMul G
local instance scalarActionBoundaryH : DistribMulAction H (ZMod 2) := scalarActionZmodTwo H
local instance scalarContinuousBoundaryH : ContinuousSMul H (ZMod 2) :=
  scalarActionZmodTwo_continuousSMul H

/-- The group-theoretic kernel input in the rigidity argument: every nontrivial kernel has a
nonzero ambient-conjugation-invariant continuous mod-two character.

For pro-`2` `G`, the expected proof passes to a finite `2`-group quotient in which the kernel
has nontrivial image, takes the elementary Frattini quotient of that image, and applies the
fixed-vector theorem to its dual. -/
def InvariantKernelCharacterSupply (f : ContinuousMonoidHom G H) : Prop :=
  (∃ n : ↥f.toMonoidHom.ker, n ≠ 1) →
    ∃ chi : ContinuousMonoidHom ↥f.toMonoidHom.ker (Multiplicative (ZMod 2)),
      IsInvariantKernelCharacter f chi ∧ ∃ n, chi n ≠ 1

/-- The exact missing continuous Hochschild--Serre five-term assertion, stated without an
unimplemented invariant-cohomology object.  Surjectivity of degree-one inflation and
injectivity of degree-two inflation force every invariant kernel character to vanish. -/
def H1H2InflationDetectsInvariantKernelCharacters
    (f : ContinuousMonoidHom G H) : Prop :=
  Function.Surjective (demushkinH1Inflation f) →
    Function.Injective (demushkinH2Inflation f) →
      ∀ chi : ContinuousMonoidHom ↥f.toMonoidHom.ker (Multiplicative (ZMod 2)),
        IsInvariantKernelCharacter f chi → ∀ n, chi n = 1

/-- The two exact kernel inputs turn low-degree inflation rigidity into injectivity of the
original epimorphism. -/
theorem injective_of_H1H2Inflation_of_invariantKernelCharacter
    (f : ContinuousMonoidHom G H)
    (hH1 : Function.Surjective (demushkinH1Inflation f))
    (hH2 : Function.Injective (demushkinH2Inflation f))
    (hdetect : H1H2InflationDetectsInvariantKernelCharacters f)
    (hsupply : InvariantKernelCharacterSupply f) :
    Function.Injective f := by
  rw [injective_iff_map_eq_one]
  intro g hg
  by_contra hg1
  let n : ↥f.toMonoidHom.ker := ⟨g, hg⟩
  have hn1 : n ≠ 1 := by
    intro hn
    apply hg1
    exact congrArg Subtype.val hn
  obtain ⟨chi, hchi, m, hm⟩ := hsupply ⟨n, hn1⟩
  exact hm (hdetect hH1 hH2 chi hchi m)

/-- **Demushkin epimorphism rigidity, reduced to the two generic kernel facts.**

A continuous surjection between positive equal-rank pro-two Demushkin groups is an isomorphism
once the low-degree five-term kernel detection and the invariant-character supply are available.
All Demushkin-specific cohomology has been discharged above. -/
theorem demushkinEpimorphism_bijective_of_kernelCharacterBoundary
    (f : ContinuousMonoidHom G H) (hf : Function.Surjective f)
    (hDG : IsDemushkin 2 G) (hDH : IsDemushkin 2 H)
    (hrank : demushkinRank 2 G = demushkinRank 2 H)
    (hrankPos : 0 < demushkinRank 2 G)
    (hdetect : H1H2InflationDetectsInvariantKernelCharacters f)
    (hsupply : InvariantKernelCharacterSupply f) :
    Function.Bijective f := by
  have hH1 := demushkinH1Inflation_bijective_of_surjective_of_rank_eq
    f hf hDG hDH hrank
  have hH2 := demushkinH2Inflation_bijective_of_demushkin_of_H1_surjective
    f hDG hDH hrankPos hH1.2
  exact ⟨injective_of_H1H2Inflation_of_invariantKernelCharacter
    f hH1.2 hH2.1 hdetect hsupply, hf⟩

end KernelBoundary

end

end GQ2.Dyadic
