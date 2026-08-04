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
import Mathlib.Topology.ContinuousMap.Basic
import Mathlib.Topology.Separation.Hausdorff

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

/-- The group-theoretic kernel input in the rigidity argument: every nontrivial kernel has a
nonzero ambient-conjugation-invariant continuous mod-two character. -/
def InvariantKernelCharacterSupply {G H : Type} [Group G] [TopologicalSpace G]
    [Group H] [TopologicalSpace H] (f : ContinuousMonoidHom G H) : Prop :=
  (∃ n : ↥f.toMonoidHom.ker, n ≠ 1) →
    ∃ chi : ContinuousMonoidHom ↥f.toMonoidHom.ker (Multiplicative (ZMod 2)),
      IsInvariantKernelCharacter f chi ∧ ∃ n, chi n ≠ 1

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

/-- Quotients by open normal subgroups of a profinite group have discrete quotient topology. -/
private theorem discreteTopology_openNormalQuotient
    {K : Type} [Group K] [TopologicalSpace K] [IsTopologicalGroup K]
    (U : OpenNormalSubgroup K) : DiscreteTopology (K ⧸ U.toSubgroup) := by
  refine discreteTopology_of_isOpen_singleton_one ?_
  have hpre : (QuotientGroup.mk : K → K ⧸ U.toSubgroup) ⁻¹' {1} =
      (U.toSubgroup : Set K) := by
    ext x
    simp only [Set.mem_preimage, Set.mem_singleton_iff, SetLike.mem_coe,
      QuotientGroup.eq_one_iff]
  rw [← (QuotientGroup.isQuotientMap_mk U.toSubgroup).isOpen_preimage, hpre]
  exact U.isOpen'

/-- A nontrivial closed normal subgroup of a profinite pro-two group has a nonzero continuous
mod-two character fixed by ambient conjugation.  The character is constructed in a finite
two-group quotient separating a chosen nontrivial kernel element, then pulled back. -/
theorem invariantKernelCharacterSupply_of_isProP
    (hG : IsProP 2 G) (f : ContinuousMonoidHom G H) :
    InvariantKernelCharacterSupply f := by
  rintro ⟨n, hn⟩
  have hnG : n.1 ≠ 1 := by
    intro h
    apply hn
    exact Subtype.ext h
  obtain ⟨U, hUsub⟩ := ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one
    (U := ({n.1}ᶜ : Set G)) isOpen_compl_singleton
    (Set.mem_compl_singleton_iff.mpr fun h ↦ hnG h.symm)
  have hnU : n.1 ∉ U := by
    intro hnmem
    exact (hUsub hnmem) rfl
  let P := G ⧸ U.toSubgroup
  let q : ContinuousMonoidHom G P := quotientMk U.toSubgroup
  letI : Finite P := Subgroup.quotient_finite_of_isOpen U.toSubgroup U.isOpen'
  letI : DiscreteTopology P := discreteTopology_openNormalQuotient U
  let Nbar : Subgroup P := f.toMonoidHom.ker.map q.toMonoidHom
  letI : Nbar.Normal := Subgroup.Normal.map (inferInstance : f.toMonoidHom.ker.Normal)
    q.toMonoidHom (quotientMk_surjective U.toSubgroup)
  let V : OpenNormalSubgroup P :=
    { toSubgroup := Nbar
      isOpen' := isOpen_discrete _ }
  let Q := P ⧸ V.toSubgroup
  let qbar : ContinuousMonoidHom P Q := quotientMk V.toSubgroup
  letI : Finite Q := Subgroup.quotient_finite_of_isOpen V.toSubgroup V.isOpen'
  letI : DiscreteTopology Q := discreteTopology_openNormalQuotient V
  have hP : IsPGroup 2 P := hG U
  let m : ↥qbar.toMonoidHom.ker := ⟨q n.1, by
    show qbar (q n.1) = 1
    rw [quotientMk_eq_one_iff]
    change q n.1 ∈ Nbar
    exact ⟨n.1, n.2, rfl⟩⟩
  have hm : m ≠ 1 := by
    intro hm1
    apply hnU
    apply (quotientMk_eq_one_iff U.toSubgroup).mp
    exact congrArg Subtype.val hm1
  obtain ⟨chiBar, hchiBar, m₀, hm₀⟩ :=
    finiteTwoGroup_invariantKernelCharacterSupply qbar
      (quotientMk_surjective V.toSubgroup) hP ⟨m, hm⟩
  have hqKer (x : ↥f.toMonoidHom.ker) : q x.1 ∈ qbar.toMonoidHom.ker := by
    show qbar (q x.1) = 1
    rw [quotientMk_eq_one_iff]
    change q x.1 ∈ Nbar
    exact ⟨x.1, x.2, rfl⟩
  let kMap : ContinuousMonoidHom ↥f.toMonoidHom.ker ↥qbar.toMonoidHom.ker :=
    { toFun := fun x ↦ ⟨q x.1, hqKer x⟩
      map_one' := Subtype.ext (map_one q)
      map_mul' := fun x y ↦ Subtype.ext (map_mul q x.1 y.1)
      continuous_toFun := Continuous.subtype_mk
        (q.continuous_toFun.comp continuous_subtype_val) hqKer }
  let chi : ContinuousMonoidHom ↥f.toMonoidHom.ker (Multiplicative (ZMod 2)) :=
    chiBar.comp kMap
  refine ⟨chi, ?_, ?_⟩
  · intro g x
    change chiBar (kMap ⟨g * x.1 * g⁻¹, _⟩) = chiBar (kMap x)
    calc
      chiBar (kMap ⟨g * x.1 * g⁻¹, _⟩) =
          chiBar ⟨q g * (kMap x).1 * (q g)⁻¹, by
            show qbar (q g * (kMap x).1 * (q g)⁻¹) = 1
            have hxker : qbar (kMap x).1 = 1 := (kMap x).2
            rw [map_mul, map_mul, map_inv, hxker]
            group⟩ := by
        apply congrArg chiBar
        apply Subtype.ext
        change q (g * x.1 * g⁻¹) = q g * q x.1 * (q g)⁻¹
        rw [map_mul, map_mul, map_inv]
      _ = chiBar (kMap x) := hchiBar (q g) (kMap x)
  · have hm₀N : m₀.1 ∈ Nbar := by
      exact (quotientMk_eq_one_iff V.toSubgroup).mp m₀.2
    obtain ⟨g, hgker, hqg⟩ := hm₀N
    let x : ↥f.toMonoidHom.ker := ⟨g, hgker⟩
    refine ⟨x, ?_⟩
    have hk : kMap x = m₀ := by
      apply Subtype.ext
      exact hqg
    change chiBar (kMap x) ≠ 1
    rw [hk]
    exact hm₀

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

/-- For a profinite pro-two source, the finite-quotient construction supplies the invariant
kernel character automatically.  Thus low-degree five-term detection alone implies injectivity. -/
theorem injective_of_H1H2Inflation_of_isProP
    (f : ContinuousMonoidHom G H) (hG : IsProP 2 G)
    (hH1 : Function.Surjective (demushkinH1Inflation f))
    (hH2 : Function.Injective (demushkinH2Inflation f))
    (hdetect : H1H2InflationDetectsInvariantKernelCharacters f) :
    Function.Injective f :=
  injective_of_H1H2Inflation_of_invariantKernelCharacter f hH1 hH2 hdetect
    (invariantKernelCharacterSupply_of_isProP hG f)

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

/-- **Demushkin epimorphism rigidity, reduced solely to Hochschild--Serre detection.**

The finite-quotient invariant-character supply is now a theorem, so the continuous five-term
kernel-detection statement is the only remaining generic input. -/
theorem demushkinEpimorphism_bijective_of_fiveTermKernelDetection
    (f : ContinuousMonoidHom G H) (hf : Function.Surjective f)
    (hDG : IsDemushkin 2 G) (hDH : IsDemushkin 2 H)
    (hrank : demushkinRank 2 G = demushkinRank 2 H)
    (hrankPos : 0 < demushkinRank 2 G)
    (hdetect : H1H2InflationDetectsInvariantKernelCharacters f) :
    Function.Bijective f :=
  demushkinEpimorphism_bijective_of_kernelCharacterBoundary f hf hDG hDH hrank hrankPos
    hdetect (invariantKernelCharacterSupply_of_isProP hDG.isProP f)

end KernelBoundary

section FiveTerm

variable {G H : Type}
  [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
  [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
  [T2Space H]

local instance scalarActionG_fiveTerm : DistribMulAction G (ZMod 2) := scalarActionZmodTwo G
local instance scalarContinuousG_fiveTerm : ContinuousSMul G (ZMod 2) :=
  scalarActionZmodTwo_continuousSMul G
local instance scalarActionH_fiveTerm : DistribMulAction H (ZMod 2) := scalarActionZmodTwo H
local instance scalarContinuousH_fiveTerm : ContinuousSMul H (ZMod 2) :=
  scalarActionZmodTwo_continuousSMul H

variable (f : ContinuousMonoidHom G H)

private abbrev EpiKernel : Subgroup G := f.toMonoidHom.ker

local instance scalarActionKernel : DistribMulAction (EpiKernel f) (ZMod 2) :=
  scalarActionZmodTwo (EpiKernel f)
local instance scalarContinuousKernel : ContinuousSMul (EpiKernel f) (ZMod 2) :=
  scalarActionZmodTwo_continuousSMul (EpiKernel f)

/-- The exact continuous-cochain input needed to construct transgression.

An arbitrary continuous extension of `chi` is not enough: its coboundary need not be constant
on kernel cosets.  The extension must satisfy `b(gn) = b(g) + chi(n)`.  Algebraically such an
extension is obtained from right-coset representatives.  Continuously, for profinite groups and
finite coefficients, one expects to choose the representatives after factoring `chi` through a
finite normal-core quotient. -/
def InvariantKernelCharacterEquivariantExtensionSupply : Prop :=
  ∀ (chi : ContinuousMonoidHom (EpiKernel f) (Multiplicative (ZMod 2))),
    IsInvariantKernelCharacter f chi →
    ∃ b : G → ZMod 2, Continuous b ∧
      (∀ n : EpiKernel f, b n.1 = Multiplicative.toAdd (chi n)) ∧
      ∀ (g : G) (n : EpiKernel f),
        b (g * n.1) = b g + Multiplicative.toAdd (chi n)

/-- Purely algebraic coset representatives extend a character of a normal subgroup to a
right-equivariant function.  The subtraction at `1` removes the arbitrary representative of
the identity coset, so the extension restricts literally to `chi`. -/
private theorem exists_rightEquivariantExtension
    {F : Type} [Group F] (N : Subgroup F) [N.Normal]
    (chi : N →* Multiplicative (ZMod 2)) :
    ∃ b : F → ZMod 2,
      (∀ n : N, b n.1 = Multiplicative.toAdd (chi n)) ∧
      ∀ (x : F) (n : N), b (x * n.1) = b x + Multiplicative.toAdd (chi n) := by
  let rep : F → F := fun x => Quotient.out (QuotientGroup.mk' N x)
  have hrep_quot (x : F) : QuotientGroup.mk' N (rep x) = QuotientGroup.mk' N x :=
    Quotient.out_eq _
  have htail (x : F) : (rep x)⁻¹ * x ∈ N := by
    apply (QuotientGroup.eq_one_iff ((rep x)⁻¹ * x)).mp
    change QuotientGroup.mk' N ((rep x)⁻¹ * x) = 1
    rw [map_mul, map_inv, hrep_quot, inv_mul_cancel]
  let tail (x : F) : N := ⟨(rep x)⁻¹ * x, htail x⟩
  have hrep_mul_N (x : F) (n : N) : rep (x * n.1) = rep x := by
    dsimp [rep]
    apply congrArg Quotient.out
    change (QuotientGroup.mk' N x) * QuotientGroup.mk' N n.1 =
      QuotientGroup.mk' N x
    have hnq : QuotientGroup.mk' N n.1 = 1 :=
      (QuotientGroup.eq_one_iff n.1).mpr n.2
    rw [hnq, mul_one]
  have htail_mul_N (x : F) (n : N) : tail (x * n.1) = tail x * n := by
    apply Subtype.ext
    dsimp [tail]
    rw [hrep_mul_N]
    group
  let raw : F → ZMod 2 := fun x => Multiplicative.toAdd (chi (tail x))
  have hraw (x : F) (n : N) : raw (x * n.1) = raw x + Multiplicative.toAdd (chi n) := by
    dsimp [raw]
    rw [htail_mul_N, map_mul]
    rfl
  let b : F → ZMod 2 := fun x => raw x - raw 1
  refine ⟨b, ?_, ?_⟩
  · intro n
    dsimp [b]
    rw [show n.1 = (1 : F) * n.1 by simp, hraw]
    abel
  · intro x n
    dsimp [b]
    rw [hraw]
    abel

/-- Every invariant continuous mod-two kernel character has the equivariant extension required
by transgression.

The character kernel is open in `ker f`.  An ambient open normal subgroup `U` is chosen whose
intersection with `ker f` lies in that kernel.  The character therefore factors through the
image of `ker f` in the finite quotient `G/U`; ordinary coset representatives there give the
extension, and pullback from the discrete finite quotient makes it continuous. -/
theorem invariantKernelCharacterEquivariantExtensionSupply :
    InvariantKernelCharacterEquivariantExtensionSupply f := by
  intro chi _hchi
  let N : Subgroup G := EpiKernel f
  let K : Subgroup N := chi.toMonoidHom.ker
  have hKopen : IsOpen (K : Set N) := by
    change IsOpen (chi ⁻¹' {1})
    exact (isOpen_discrete {1}).preimage chi.continuous_toFun
  obtain ⟨O, hOopen, hOK⟩ := isOpen_induced_iff.mp hKopen
  have h1O : (1 : G) ∈ O := by
    have h1K : (1 : N) ∈ Subtype.val ⁻¹' O := by
      rw [hOK]
      exact K.one_mem
    exact h1K
  obtain ⟨U, hUO⟩ :=
    ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one hOopen h1O
  let F : Type := G ⧸ U.toSubgroup
  letI : DiscreteTopology F := QuotientGroup.discreteTopology U.isOpen
  letI : Finite F := Subgroup.quotient_finite_of_isOpen U.toSubgroup U.isOpen
  let q : ContinuousMonoidHom G F := GQ2.quotientMk U.toSubgroup
  let Nbar : Subgroup F := N.map q.toMonoidHom
  letI : Nbar.Normal :=
    Subgroup.Normal.map (inferInstance : N.Normal) q.toMonoidHom
      (GQ2.quotientMk_surjective U.toSubgroup)
  let qN : ContinuousMonoidHom N Nbar := {
    toFun := fun n => ⟨q n.1, Subgroup.mem_map_of_mem q.toMonoidHom n.2⟩
    map_one' := Subtype.ext (map_one q)
    map_mul' := fun n m => Subtype.ext (map_mul q n.1 m.1)
    continuous_toFun := by
      apply continuous_induced_rng.mpr
      exact q.continuous_toFun.comp continuous_subtype_val }
  have hqN : Function.Surjective qN := by
    intro y
    obtain ⟨g, hgN, hgy⟩ := y.2
    exact ⟨⟨g, hgN⟩, Subtype.ext hgy⟩
  have hqNker : qN.toMonoidHom.ker ≤ chi.toMonoidHom.ker := by
    intro n hn
    have hnqN : qN n = 1 := MonoidHom.mem_ker.mp hn
    have hnq : q n.1 = 1 := congrArg Subtype.val hnqN
    have hnU : n.1 ∈ U.toSubgroup :=
      (QuotientGroup.eq_one_iff n.1).mp hnq
    have hnO : n.1 ∈ O := hUO hnU
    have hnK : n ∈ K := by
      have : n ∈ Subtype.val ⁻¹' O := hnO
      rwa [hOK] at this
    exact hnK
  let chiBarHom : Nbar →* Multiplicative (ZMod 2) :=
    qN.toMonoidHom.liftOfSurjective hqN ⟨chi.toMonoidHom, hqNker⟩
  let chiBar : ContinuousMonoidHom Nbar (Multiplicative (ZMod 2)) :=
    ⟨chiBarHom, continuous_of_discreteTopology⟩
  have hchiBar (n : N) : chiBar (qN n) = chi n := by
    exact qN.toMonoidHom.liftOfRightInverse_comp_apply
      (Function.surjInv hqN) (Function.rightInverse_surjInv hqN)
      ⟨chi.toMonoidHom, hqNker⟩ n
  obtain ⟨bbar, hbbarN, hbbar⟩ :=
    exists_rightEquivariantExtension Nbar chiBar.toMonoidHom
  let b : G → ZMod 2 := fun g => bbar (q g)
  refine ⟨b, continuous_of_discreteTopology.comp q.continuous_toFun, ?_, ?_⟩
  · intro n
    change bbar (q n.1) = Multiplicative.toAdd (chi n)
    have h := hbbarN (qN n)
    change bbar (q n.1) = Multiplicative.toAdd (chiBar (qN n)) at h
    rw [hchiBar] at h
    exact h
  · intro g n
    change bbar (q (g * n.1)) = bbar (q g) + Multiplicative.toAdd (chi n)
    rw [map_mul]
    have h := hbbar (q g) (qN n)
    change bbar (q g * q n.1) =
      bbar (q g) + Multiplicative.toAdd (chiBar (qN n)) at h
    rw [hchiBar] at h
    exact h

private theorem equivariantExtension_coboundary_right_coset
    (chi : ContinuousMonoidHom (EpiKernel f) (Multiplicative (ZMod 2)))
    (b : G → ZMod 2)
    (hb : ∀ (g : G) (n : EpiKernel f),
      b (g * n.1) = b g + Multiplicative.toAdd (chi n))
    (g h : G) (n : EpiKernel f) :
    dOne G (ZMod 2) b (g, h * n.1) = dOne G (ZMod 2) b (g, h) := by
  simp only [dOne, AddMonoidHom.coe_mk, ZeroHom.coe_mk,
    scalarActionZmodTwo_triv G]
  rw [hb h n, show g * (h * n.1) = (g * h) * n.1 by group, hb (g * h) n]
  abel

private theorem equivariantExtension_coboundary_left_coset
    (chi : ContinuousMonoidHom (EpiKernel f) (Multiplicative (ZMod 2)))
    (hchi : IsInvariantKernelCharacter f chi)
    (b : G → ZMod 2)
    (hb : ∀ (g : G) (n : EpiKernel f),
      b (g * n.1) = b g + Multiplicative.toAdd (chi n))
    (g h : G) (n : EpiKernel f) :
    dOne G (ZMod 2) b (g * n.1, h) = dOne G (ZMod 2) b (g, h) := by
  let nh : EpiKernel f := ⟨h⁻¹ * n.1 * h, by
    change f (h⁻¹ * n.1 * h) = 1
    have hn : f n.1 = 1 := n.2
    rw [map_mul, map_mul, map_inv, hn, mul_one, inv_mul_cancel]⟩
  have hmul : (g * n.1) * h = (g * h) * nh.1 := by
    dsimp [nh]
    group
  have hchin : Multiplicative.toAdd (chi nh) = Multiplicative.toAdd (chi n) := by
    have hval := congrArg Multiplicative.toAdd (hchi h⁻¹ n)
    convert hval using 1
    apply congrArg (fun m : EpiKernel f => Multiplicative.toAdd (chi m))
    apply Subtype.ext
    simp [nh]
  simp only [dOne, AddMonoidHom.coe_mk, ZeroHom.coe_mk,
    scalarActionZmodTwo_triv G]
  rw [hmul, hb (g * h) nh, hb g n, hchin]
  abel

/-- An equivariant extension gives the literal continuous transgression cocycle downstairs.

The quotient-map lift is along `f × f`; no continuous section of `f` is assumed. -/
private theorem exists_kernelCharacter_transgressionCocycle
    (hf : Function.Surjective f)
    (chi : ContinuousMonoidHom (EpiKernel f) (Multiplicative (ZMod 2)))
    (hchi : IsInvariantKernelCharacter f chi)
    (b : G → ZMod 2) (hbcont : Continuous b)
    (hb : ∀ (g : G) (n : EpiKernel f),
      b (g * n.1) = b g + Multiplicative.toAdd (chi n)) :
    ∃ c : Z2 H (ZMod 2), ∀ g h : G,
      c.1 (f g, f h) = dOne G (ZMod 2) b (g, h) := by
  let f2 : C(G × G, H × H) :=
    ⟨fun p => (f p.1, f p.2),
      (f.continuous_toFun.comp continuous_fst).prodMk
        (f.continuous_toFun.comp continuous_snd)⟩
  have hf2 : Function.Surjective f2 := by
    rintro ⟨x, y⟩
    obtain ⟨g, rfl⟩ := hf x
    obtain ⟨h, rfl⟩ := hf y
    exact ⟨(g, h), rfl⟩
  have hq : Topology.IsQuotientMap f2 :=
    IsQuotientMap.of_surjective_continuous hf2 f2.continuous
  let db : C(G × G, ZMod 2) :=
    ⟨dOne G (ZMod 2) b,
      ((continuous_fst.smul (hbcont.comp continuous_snd)).sub
        (hbcont.comp (continuous_fst.mul continuous_snd))).add
          (hbcont.comp continuous_fst)⟩
  have hfactor : Function.FactorsThrough db f2 := by
    rintro ⟨g₁, h₁⟩ ⟨g₂, h₂⟩ hp
    have hg : f g₁ = f g₂ := congrArg Prod.fst hp
    have hh : f h₁ = f h₂ := congrArg Prod.snd hp
    let ng : EpiKernel f := ⟨g₁⁻¹ * g₂, by
      change f (g₁⁻¹ * g₂) = 1
      rw [map_mul, map_inv, hg, inv_mul_cancel]⟩
    let nh : EpiKernel f := ⟨h₁⁻¹ * h₂, by
      change f (h₁⁻¹ * h₂) = 1
      rw [map_mul, map_inv, hh, inv_mul_cancel]⟩
    have hgmul : g₁ * ng.1 = g₂ := by dsimp [ng]; group
    have hhmul : h₁ * nh.1 = h₂ := by dsimp [nh]; group
    change dOne G (ZMod 2) b (g₁, h₁) = dOne G (ZMod 2) b (g₂, h₂)
    rw [← hgmul, ← hhmul,
      equivariantExtension_coboundary_left_coset f chi hchi b hb,
      equivariantExtension_coboundary_right_coset f chi b hb]
  let bar : C(H × H, ZMod 2) := hq.lift db hfactor
  have hbar (g h : G) : bar (f g, f h) = dOne G (ZMod 2) b (g, h) := by
    have happ := congrArg (fun k : C(G × G, ZMod 2) => k (g, h))
      (Topology.IsQuotientMap.lift_comp hq db hfactor)
    exact happ
  have hbarZ2 : (bar : H × H → ZMod 2) ∈ Z2 H (ZMod 2) := by
    refine mem_Z2_iff.mpr ⟨bar.continuous, ?_⟩
    intro x y z
    obtain ⟨g, rfl⟩ := hf x
    obtain ⟨h, rfl⟩ := hf y
    obtain ⟨k, rfl⟩ := hf z
    rw [hbar h k, ← map_mul, hbar g (h * k), ← map_mul,
      hbar (g * h) k, hbar g h]
    have hcob : dOne G (ZMod 2) b ∈ Z2 G (ZMod 2) := by
      apply B2_le_Z2
      exact ⟨b, hbcont, rfl⟩
    exact (mem_Z2_iff.mp hcob).2 g h k
  exact ⟨⟨bar, hbarZ2⟩, hbar⟩

/-- The transgression of an invariant kernel character always inflates to zero: its pullback is
the explicit coboundary `d¹ b`. -/
private theorem kernelCharacter_transgression_inflation_eq_zero
    (hf : Function.Surjective f)
    (chi : ContinuousMonoidHom (EpiKernel f) (Multiplicative (ZMod 2)))
    (hchi : IsInvariantKernelCharacter f chi)
    (b : G → ZMod 2) (hbcont : Continuous b)
    (hb : ∀ (g : G) (n : EpiKernel f),
      b (g * n.1) = b g + Multiplicative.toAdd (chi n)) :
    ∃ c : Z2 H (ZMod 2),
      demushkinH2Inflation f (H2mk H (ZMod 2) c) = 0 ∧
      ∀ g h : G, c.1 (f g, f h) = dOne G (ZMod 2) b (g, h) := by
  obtain ⟨c, hc⟩ :=
    exists_kernelCharacter_transgressionCocycle f hf chi hchi b hbcont hb
  refine ⟨c, ?_, hc⟩
  rw [demushkinH2Inflation, inf2_H2mk]
  apply (QuotientAddGroup.eq_zero_iff _).mpr
  rw [AddSubgroup.mem_addSubgroupOf]
  refine ⟨b, hbcont, ?_⟩
  funext p
  exact (hc p.1 p.2).symm

/-- The explicit continuous-cochain five-term argument.

Injectivity in degree two kills the transgression.  A primitive downstairs then changes the
equivariant extension into an ambient one-cocycle extending `chi`.  Surjectivity in degree one
forces that ambient cocycle to descend from `H`, and hence to vanish on `ker f`. -/
theorem h1H2InflationDetectsInvariantKernelCharacters_of_equivariantExtension
    (hf : Function.Surjective f)
    (hext : InvariantKernelCharacterEquivariantExtensionSupply f) :
    H1H2InflationDetectsInvariantKernelCharacters f := by
  intro hH1 hH2 chi hchi
  obtain ⟨b, hbcont, hbker, hb⟩ := hext chi hchi
  obtain ⟨c, hcinf, hc⟩ :=
    kernelCharacter_transgression_inflation_eq_zero f hf chi hchi b hbcont hb
  have hc0 : H2mk H (ZMod 2) c = 0 := hH2 (by simpa using hcinf)
  have hcmem := (QuotientAddGroup.eq_zero_iff c).mp hc0
  rw [AddSubgroup.mem_addSubgroupOf] at hcmem
  obtain ⟨a, hacont, ha⟩ := hcmem
  let zfun : G → ZMod 2 := fun g => b g - a (f g)
  have hzcont : Continuous zfun := hbcont.sub (hacont.comp f.continuous_toFun)
  have hzmem : zfun ∈ Z1 G (ZMod 2) := by
    refine mem_Z1_iff.mpr ⟨hzcont, ?_⟩
    intro g h
    have hca := congrFun ha (f g, f h)
    change dOne H (ZMod 2) a (f g, f h) = c.1 (f g, f h) at hca
    rw [hc] at hca
    simp only [dOne, AddMonoidHom.coe_mk, ZeroHom.coe_mk,
      scalarActionZmodTwo_triv H, scalarActionZmodTwo_triv G] at hca ⊢
    dsimp [zfun]
    rw [map_mul]
    rw [← sub_eq_zero]
    rw [← sub_eq_zero] at hca
    abel_nf at hca ⊢
    exact hca
  let z : Z1 G (ZMod 2) := ⟨zfun, hzmem⟩
  have hb1 : b 1 = 0 := by
    change b (1 : EpiKernel f).1 = 0
    rw [hbker (1 : EpiKernel f)]
    change Multiplicative.toAdd (chi 1) = 0
    rw [map_one]
    rfl
  have ha1 : a 1 = 0 := by
    have hz1 := Z1_apply_one z
    change b 1 - a (f 1) = 0 at hz1
    simpa [hb1] using hz1
  obtain ⟨x, hx⟩ := hH1 (H1mk G (ZMod 2) z)
  obtain ⟨w, rfl⟩ := H1mk_surjective (G := H) (M := ZMod 2) x
  rw [demushkinH1Inflation, inf1_H1mk] at hx
  have hmk_inj : Function.Injective (H1mk G (ZMod 2)) := by
    apply (injective_iff_map_eq_zero _).mpr
    intro u hu
    have hmem := (QuotientAddGroup.eq_zero_iff u).mp hu
    rw [AddSubgroup.mem_addSubgroupOf,
      B1_eq_bot_of_trivial (scalarActionZmodTwo_triv G), AddSubgroup.mem_bot] at hmem
    exact Subtype.ext hmem
  have hxz := hmk_inj hx
  intro n
  have hn : f n.1 = 1 := n.2
  have hw1 : w.1 1 = 0 := Z1_apply_one w
  have hzn : z.1 n.1 = 0 := by
    have happ := congrArg (fun u : Z1 G (ZMod 2) => u.1 n.1) hxz
    simpa only [Z1comap, AddMonoidHom.coe_mk, ZeroHom.coe_mk,
      AddMonoidHom.id_apply, hn, hw1] using happ.symm
  apply Multiplicative.toAdd.injective
  change Multiplicative.toAdd (chi n) = 0
  have hzker : z.1 n.1 = Multiplicative.toAdd (chi n) := by
    change b n.1 - a (f n.1) = Multiplicative.toAdd (chi n)
    rw [hbker n, hn, ha1, sub_zero]
  exact hzker ▸ hzn

/-- **Continuous Hochschild--Serre five-term kernel detection.**

For a continuous epimorphism of profinite groups, surjectivity of mod-two degree-one inflation
and injectivity of degree-two inflation force every ambient-conjugation-invariant continuous
mod-two character of the kernel to vanish.  The proof is fully explicit in continuous
inhomogeneous cochains; no five-term exact-sequence API or continuous section is assumed. -/
theorem h1H2InflationDetectsInvariantKernelCharacters
    (hf : Function.Surjective f) :
    H1H2InflationDetectsInvariantKernelCharacters f :=
  h1H2InflationDetectsInvariantKernelCharacters_of_equivariantExtension f hf
    (invariantKernelCharacterEquivariantExtensionSupply f)

/-- **Equal-rank Demushkin epimorphism rigidity.**

A continuous epimorphism between positive equal-rank profinite pro-two Demushkin groups is
bijective.  The proof combines low-degree Demushkin cup-product rigidity with the explicit
continuous Hochschild--Serre five-term argument above. -/
theorem demushkinEpimorphism_bijective
    (hf : Function.Surjective f)
    (hDG : IsDemushkin 2 G) (hDH : IsDemushkin 2 H)
    (hrank : demushkinRank 2 G = demushkinRank 2 H)
    (hrankPos : 0 < demushkinRank 2 G) :
    Function.Bijective f :=
  demushkinEpimorphism_bijective_of_fiveTermKernelDetection
    f hf hDG hDH hrank hrankPos
    (h1H2InflationDetectsInvariantKernelCharacters f hf)

end FiveTerm

end

end GQ2.Dyadic
