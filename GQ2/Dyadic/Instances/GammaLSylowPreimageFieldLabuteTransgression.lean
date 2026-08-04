/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using OpenAI Codex
-/
import GQ2.Dyadic.Instances.GammaLSylowPreimageFieldLabuteReverse

/-!
# Schreier transgression for the first lower two-central extension

This file constructs the canonical cochain-level map from the dual of `lambda_2/lambda_3`
to the kernel of degree-two inflation from `G/lambda_2`.  It is the concrete low-degree
Hochschild--Serre transgression: a set-theoretic section gives a factor set in `lambda_2`,
which a character evaluates to an `F_2`-valued two-cocycle.  The inflated cocycle is the
explicit coboundary of the corresponding kernel-component cochain.
-/

namespace GQ2.Dyadic.LSquare

noncomputable section

open GQ2 GQ2.Roe.Labute ContCoh
open scoped commutatorElement

section Defect

variable (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- The chosen set-theoretic section of `G -> G/lambda_2`. -/
def lowerTwoCentralSection (q : levelQuot G 2) : G := by
  classical
  exact if q = 1 then 1 else Quotient.out q

@[simp] theorem lowerTwoCentralSection_one :
    lowerTwoCentralSection G 1 = 1 := by
  simp [lowerTwoCentralSection]

@[simp] theorem levelMk_lowerTwoCentralSection (q : levelQuot G 2) :
    levelMk G 2 (lowerTwoCentralSection G q) = q := by
  classical
  by_cases hq : q = 1
  · simp [lowerTwoCentralSection, hq]
  · rw [lowerTwoCentralSection, if_neg hq]
    exact QuotientGroup.out_eq' q

/-- The section factor set, projected from `lambda_2` to `lambda_2/lambda_3`. -/
def lowerTwoCentralSectionDefect (q r : levelQuot G 2) : zLayer G 2 := by
  let x := lowerTwoCentralSection G q * lowerTwoCentralSection G r *
    (lowerTwoCentralSection G (q * r))⁻¹
  have hx : x ∈ twoCentralSeries G 2 := by
    apply (QuotientGroup.eq_one_iff x).mp
    change levelMk G 2 x = 1
    dsimp [x]
    rw [map_mul, map_mul, map_inv, levelMk_lowerTwoCentralSection,
      levelMk_lowerTwoCentralSection, levelMk_lowerTwoCentralSection]
    group
  exact ⟨levelMk G 3 x, ⟨x, hx, rfl⟩⟩

/-- The kernel component of an ambient element relative to the chosen section, projected to
`lambda_2/lambda_3`. -/
def lowerTwoCentralKernelPart (g : G) : zLayer G 2 := by
  let x := g * (lowerTwoCentralSection G (levelMk G 2 g))⁻¹
  have hx : x ∈ twoCentralSeries G 2 := by
    apply (QuotientGroup.eq_one_iff x).mp
    change levelMk G 2 x = 1
    dsimp [x]
    rw [map_mul, map_inv, levelMk_lowerTwoCentralSection]
    group
  exact ⟨levelMk G 3 x, ⟨x, hx, rfl⟩⟩

@[simp] theorem lowerTwoCentralSectionDefect_one_one :
    lowerTwoCentralSectionDefect G 1 1 = 1 := by
  apply Subtype.ext
  simp [lowerTwoCentralSectionDefect]

@[simp] theorem lowerTwoCentralKernelPart_one :
    lowerTwoCentralKernelPart G 1 = 1 := by
  apply Subtype.ext
  simp [lowerTwoCentralKernelPart]

/-- On `lambda_2`, the kernel component is the element itself modulo `lambda_3`. -/
theorem lowerTwoCentralKernelPart_coe_of_mem
    {g : G} (hg : g ∈ twoCentralSeries G 2) :
    (lowerTwoCentralKernelPart G g).1 = levelMk G 3 g := by
  have hq : levelMk G 2 g = 1 := (QuotientGroup.eq_one_iff g).mpr hg
  dsimp [lowerTwoCentralKernelPart]
  rw [hq, lowerTwoCentralSection_one]
  simp

/-- The factor set satisfies the additive cocycle identity after projection to the central
layer `lambda_2/lambda_3`. -/
theorem lowerTwoCentralSectionDefect_cocycle (g h k : levelQuot G 2) :
    Additive.ofMul (lowerTwoCentralSectionDefect G h k) +
        Additive.ofMul (lowerTwoCentralSectionDefect G g (h * k)) =
      Additive.ofMul (lowerTwoCentralSectionDefect G (g * h) k) +
        Additive.ofMul (lowerTwoCentralSectionDefect G g h) := by
  apply Additive.toMul.injective
  apply Subtype.ext
  change (lowerTwoCentralSectionDefect G h k).1 *
      (lowerTwoCentralSectionDefect G g (h * k)).1 =
    (lowerTwoCentralSectionDefect G (g * h) k).1 *
      (lowerTwoCentralSectionDefect G g h).1
  have hcentral := Subgroup.mem_center_iff.mp
    (zLayer_le_center G 2 (lowerTwoCentralSectionDefect G h k).2)
    (levelMk G 3 (lowerTwoCentralSection G g))
  have hright := Subgroup.mem_center_iff.mp
    (zLayer_le_center G 2 (lowerTwoCentralSectionDefect G (g * h) k).2)
    (lowerTwoCentralSectionDefect G g h).1
  change levelMk G 3 (lowerTwoCentralSection G g) *
      levelMk G 3 (lowerTwoCentralSection G h * lowerTwoCentralSection G k *
        (lowerTwoCentralSection G (h * k))⁻¹) =
    levelMk G 3 (lowerTwoCentralSection G h * lowerTwoCentralSection G k *
        (lowerTwoCentralSection G (h * k))⁻¹) *
      levelMk G 3 (lowerTwoCentralSection G g) at hcentral
  dsimp [lowerTwoCentralSectionDefect] at hright ⊢
  simp only [map_mul, map_inv] at hcentral hright ⊢
  let sg := levelMk G 3 (lowerTwoCentralSection G g)
  let sh := levelMk G 3 (lowerTwoCentralSection G h)
  let sk := levelMk G 3 (lowerTwoCentralSection G k)
  let shk := levelMk G 3 (lowerTwoCentralSection G (h * k))
  let sgh := levelMk G 3 (lowerTwoCentralSection G (g * h))
  let sghk := levelMk G 3 (lowerTwoCentralSection G (g * h * k))
  change sg * (sh * sk * shk⁻¹) = (sh * sk * shk⁻¹) * sg at hcentral
  change (sg * sh * sgh⁻¹) * (sgh * sk * sghk⁻¹) =
    (sgh * sk * sghk⁻¹) * (sg * sh * sgh⁻¹) at hright
  rw [← mul_assoc g h k]
  change (sh * sk * shk⁻¹) * (sg * shk * sghk⁻¹) =
    (sgh * sk * sghk⁻¹) * (sg * sh * sgh⁻¹)
  calc
    (sh * sk * shk⁻¹) * (sg * shk * sghk⁻¹) =
        ((sh * sk * shk⁻¹) * sg) * shk * sghk⁻¹ := by group
    _ = (sg * (sh * sk * shk⁻¹)) * shk * sghk⁻¹ := by rw [← hcentral]
    _ = (sg * sh * sgh⁻¹) * (sgh * sk * sghk⁻¹) := by group
    _ = (sgh * sk * sghk⁻¹) * (sg * sh * sgh⁻¹) := hright

/-- Kernel components multiply by the section factor set, after passage to the central
layer. -/
theorem lowerTwoCentralKernelPart_mul (g h : G) :
    Additive.ofMul (lowerTwoCentralKernelPart G (g * h)) =
      Additive.ofMul (lowerTwoCentralKernelPart G g) +
        Additive.ofMul (lowerTwoCentralKernelPart G h) +
          Additive.ofMul
            (lowerTwoCentralSectionDefect G (levelMk G 2 g) (levelMk G 2 h)) := by
  apply Additive.toMul.injective
  apply Subtype.ext
  change (lowerTwoCentralKernelPart G (g * h)).1 =
    (lowerTwoCentralKernelPart G g).1 * (lowerTwoCentralKernelPart G h).1 *
      (lowerTwoCentralSectionDefect G (levelMk G 2 g) (levelMk G 2 h)).1
  have hcentral := Subgroup.mem_center_iff.mp
    (zLayer_le_center G 2 (lowerTwoCentralKernelPart G h).2)
    (levelMk G 3 (lowerTwoCentralSection G (levelMk G 2 g)))
  change levelMk G 3 (lowerTwoCentralSection G (levelMk G 2 g)) *
      levelMk G 3 (h * (lowerTwoCentralSection G (levelMk G 2 h))⁻¹) =
    levelMk G 3 (h * (lowerTwoCentralSection G (levelMk G 2 h))⁻¹) *
      levelMk G 3 (lowerTwoCentralSection G (levelMk G 2 g)) at hcentral
  dsimp [lowerTwoCentralKernelPart, lowerTwoCentralSectionDefect]
  simp only [map_mul, map_inv] at hcentral ⊢
  let gg := levelMk G 3 g
  let hh := levelMk G 3 h
  let sg := levelMk G 3 (lowerTwoCentralSection G (levelMk G 2 g))
  let sh := levelMk G 3 (lowerTwoCentralSection G (levelMk G 2 h))
  let sgh := levelMk G 3
    (lowerTwoCentralSection G (levelMk G 2 g * levelMk G 2 h))
  change sg * (hh * sh⁻¹) = (hh * sh⁻¹) * sg at hcentral
  change gg * hh * sgh⁻¹ =
    gg * sg⁻¹ * (hh * sh⁻¹) * (sg * sh * sgh⁻¹)
  have hcomm : Commute sg (hh * sh⁻¹) := hcentral
  calc
    gg * hh * sgh⁻¹ = gg * (hh * sh⁻¹) * sg⁻¹ * (sg * sh * sgh⁻¹) := by group
    _ = gg * ((hh * sh⁻¹) * sg⁻¹) * (sg * sh * sgh⁻¹) := by group
    _ = gg * (sg⁻¹ * (hh * sh⁻¹)) * (sg * sh * sgh⁻¹) := by
      rw [← hcomm.inv_left.eq]
    _ = gg * sg⁻¹ * (hh * sh⁻¹) * (sg * sh * sgh⁻¹) := by group

end Defect

section Cocycle

variable (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]

/-- Evaluating the section factor set by a layer character gives a continuous
`F_2`-valued two-cocycle on `G/lambda_2`. -/
noncomputable def lowerTwoCentralTransgressionCocycle
    (hfg : IsTopologicallyFinGen G) (hpro : IsProP 2 G)
    (chi : Additive (zLayer G 2) →+ ZMod 2) :
    let Q := levelQuot G 2
    letI : DiscreteTopology Q := discreteTopology_levelQuot G hfg hpro 2
    letI : DistribMulAction Q (ZMod 2) := scalarActionZmodTwo Q
    letI : ContinuousSMul Q (ZMod 2) := scalarActionZmodTwo_continuousSMul Q
    Z2 Q (ZMod 2) := by
  let Q := levelQuot G 2
  letI : DiscreteTopology Q := discreteTopology_levelQuot G hfg hpro 2
  letI : DistribMulAction Q (ZMod 2) := scalarActionZmodTwo Q
  letI : ContinuousSMul Q (ZMod 2) := scalarActionZmodTwo_continuousSMul Q
  refine ⟨fun p => chi (Additive.ofMul (lowerTwoCentralSectionDefect G p.1 p.2)), ?_⟩
  apply mem_Z2_iff.mpr
  refine ⟨continuous_of_discreteTopology, ?_⟩
  intro g h k
  change chi (Additive.ofMul (lowerTwoCentralSectionDefect G h k)) +
      chi (Additive.ofMul (lowerTwoCentralSectionDefect G g (h * k))) =
    chi (Additive.ofMul (lowerTwoCentralSectionDefect G (g * h) k)) +
      chi (Additive.ofMul (lowerTwoCentralSectionDefect G g h))
  rw [← map_add, lowerTwoCentralSectionDefect_cocycle, map_add]

/-- The section-defect construction is additive in the layer character. -/
noncomputable def lowerTwoCentralTransgressionZ2
    (hfg : IsTopologicallyFinGen G) (hpro : IsProP 2 G) :
    let Q := levelQuot G 2
    letI : DiscreteTopology Q := discreteTopology_levelQuot G hfg hpro 2
    letI : DistribMulAction Q (ZMod 2) := scalarActionZmodTwo Q
    letI : ContinuousSMul Q (ZMod 2) := scalarActionZmodTwo_continuousSMul Q
    (Additive (zLayer G 2) →+ ZMod 2) →+ Z2 Q (ZMod 2) := by
  let Q := levelQuot G 2
  letI : DiscreteTopology Q := discreteTopology_levelQuot G hfg hpro 2
  letI : DistribMulAction Q (ZMod 2) := scalarActionZmodTwo Q
  letI : ContinuousSMul Q (ZMod 2) := scalarActionZmodTwo_continuousSMul Q
  exact
    { toFun := lowerTwoCentralTransgressionCocycle G hfg hpro
      map_zero' := by
        apply Subtype.ext
        funext p
        rfl
      map_add' := by
        intro chi psi
        apply Subtype.ext
        funext p
        rfl }

/-- The cohomology-level transgression before restricting its codomain to the inflation
kernel. -/
noncomputable def lowerTwoCentralTransgressionH2
    (hfg : IsTopologicallyFinGen G) (hpro : IsProP 2 G) :
    let Q := levelQuot G 2
    letI : DiscreteTopology Q := discreteTopology_levelQuot G hfg hpro 2
    letI : DistribMulAction Q (ZMod 2) := scalarActionZmodTwo Q
    letI : ContinuousSMul Q (ZMod 2) := scalarActionZmodTwo_continuousSMul Q
    (Additive (zLayer G 2) →+ ZMod 2) →+ H2 Q (ZMod 2) := by
  let Q := levelQuot G 2
  letI : DiscreteTopology Q := discreteTopology_levelQuot G hfg hpro 2
  letI : DistribMulAction Q (ZMod 2) := scalarActionZmodTwo Q
  letI : ContinuousSMul Q (ZMod 2) := scalarActionZmodTwo_continuousSMul Q
  exact (H2mk Q (ZMod 2)).comp (lowerTwoCentralTransgressionZ2 G hfg hpro)

/-- The continuous one-cochain whose coboundary is the inflated section-defect cocycle. -/
noncomputable def lowerTwoCentralKernelPartC1
    (hfg : IsTopologicallyFinGen G) (hpro : IsProP 2 G)
    (chi : Additive (zLayer G 2) →+ ZMod 2) :
    letI : DistribMulAction G (ZMod 2) := scalarActionZmodTwo G
    letI : ContinuousSMul G (ZMod 2) := scalarActionZmodTwo_continuousSMul G
    C1 G (ZMod 2) := by
  letI : DistribMulAction G (ZMod 2) := scalarActionZmodTwo G
  letI : ContinuousSMul G (ZMod 2) := scalarActionZmodTwo_continuousSMul G
  let Q := levelQuot G 2
  let Q3 := levelQuot G 3
  letI : DiscreteTopology Q := discreteTopology_levelQuot G hfg hpro 2
  letI : DiscreteTopology Q3 := discreteTopology_levelQuot G hfg hpro 3
  refine ⟨fun g => chi (Additive.ofMul (lowerTwoCentralKernelPart G g)), ?_⟩
  have hsection : Continuous (lowerTwoCentralSection G : Q → G) :=
    continuous_of_discreteTopology
  have hraw : Continuous fun g : G =>
      levelMk G 3 (g * (lowerTwoCentralSection G (levelMk G 2 g))⁻¹) :=
    (continuous_levelMk G 3).comp
      (continuous_id.mul ((hsection.comp (continuous_levelMk G 2)).inv))
  have hpart : Continuous (lowerTwoCentralKernelPart G : G → zLayer G 2) := by
    exact Continuous.subtype_mk hraw _
  have hchi : Continuous fun z : zLayer G 2 => chi (Additive.ofMul z) :=
    continuous_of_discreteTopology
  exact hchi.comp hpart

/-- Cochain identity exhibiting the inflated transgression cocycle as an explicit
coboundary. -/
theorem lowerTwoCentralTransgression_inflated_eq_dOne
    (hfg : IsTopologicallyFinGen G) (hpro : IsProP 2 G)
    (chi : Additive (zLayer G 2) →+ ZMod 2) :
    letI : DistribMulAction G (ZMod 2) := scalarActionZmodTwo G
    letI : ContinuousSMul G (ZMod 2) := scalarActionZmodTwo_continuousSMul G
    let Q := levelQuot G 2
    letI : DiscreteTopology Q := discreteTopology_levelQuot G hfg hpro 2
    letI : DistribMulAction Q (ZMod 2) := scalarActionZmodTwo Q
    letI : ContinuousSMul Q (ZMod 2) := scalarActionZmodTwo_continuousSMul Q
    (Z2comap ⟨levelMk G 2, continuous_levelMk G 2⟩ (AddMonoidHom.id (ZMod 2))
      continuous_id (fun _ _ => rfl)
      (lowerTwoCentralTransgressionCocycle G hfg hpro chi)).1 =
        dOne G (ZMod 2) (lowerTwoCentralKernelPartC1 G hfg hpro chi).1 := by
  letI : DistribMulAction G (ZMod 2) := scalarActionZmodTwo G
  letI : ContinuousSMul G (ZMod 2) := scalarActionZmodTwo_continuousSMul G
  let Q := levelQuot G 2
  letI : DiscreteTopology Q := discreteTopology_levelQuot G hfg hpro 2
  letI : DistribMulAction Q (ZMod 2) := scalarActionZmodTwo Q
  letI : ContinuousSMul Q (ZMod 2) := scalarActionZmodTwo_continuousSMul Q
  funext p
  obtain ⟨g, h⟩ := p
  have hmul := congrArg chi (lowerTwoCentralKernelPart_mul G g h)
  rw [map_add, map_add] at hmul
  change chi (Additive.ofMul
      (lowerTwoCentralSectionDefect G (levelMk G 2 g) (levelMk G 2 h))) =
    chi (Additive.ofMul (lowerTwoCentralKernelPart G h)) -
      chi (Additive.ofMul (lowerTwoCentralKernelPart G (g * h))) +
        chi (Additive.ofMul (lowerTwoCentralKernelPart G g))
  have hneg (x : ZMod 2) : x = -x := by
    exact eq_neg_of_add_eq_zero_left (CharTwo.add_self_eq_zero x)
  calc
    chi (Additive.ofMul
        (lowerTwoCentralSectionDefect G (levelMk G 2 g) (levelMk G 2 h))) =
        -chi (Additive.ofMul
          (lowerTwoCentralSectionDefect G (levelMk G 2 g) (levelMk G 2 h))) := hneg _
    _ = chi (Additive.ofMul (lowerTwoCentralKernelPart G h)) -
          (chi (Additive.ofMul (lowerTwoCentralKernelPart G g)) +
            chi (Additive.ofMul (lowerTwoCentralKernelPart G h)) +
              chi (Additive.ofMul
                (lowerTwoCentralSectionDefect G (levelMk G 2 g) (levelMk G 2 h)))) +
            chi (Additive.ofMul (lowerTwoCentralKernelPart G g)) := by abel
    _ = chi (Additive.ofMul (lowerTwoCentralKernelPart G h)) -
          chi (Additive.ofMul (lowerTwoCentralKernelPart G (g * h))) +
            chi (Additive.ofMul (lowerTwoCentralKernelPart G g)) := by rw [hmul]

/-- Every transgressed class lies in the kernel of canonical degree-two inflation. -/
theorem lowerTwoCentralTransgressionH2_mem_inflationKernel
    (hfg : IsTopologicallyFinGen G) (hpro : IsProP 2 G)
    (chi : Additive (zLayer G 2) →+ ZMod 2) :
    letI : DistribMulAction G (ZMod 2) := scalarActionZmodTwo G
    letI : ContinuousSMul G (ZMod 2) := scalarActionZmodTwo_continuousSMul G
    let Q := levelQuot G 2
    letI : DiscreteTopology Q := discreteTopology_levelQuot G hfg hpro 2
    letI : DistribMulAction Q (ZMod 2) := scalarActionZmodTwo Q
    letI : ContinuousSMul Q (ZMod 2) := scalarActionZmodTwo_continuousSMul Q
    lowerTwoCentralTransgressionH2 G hfg hpro chi ∈
      (lowerTwoCentralH2Inflation G).ker := by
  letI : DistribMulAction G (ZMod 2) := scalarActionZmodTwo G
  letI : ContinuousSMul G (ZMod 2) := scalarActionZmodTwo_continuousSMul G
  let Q := levelQuot G 2
  letI : DiscreteTopology Q := discreteTopology_levelQuot G hfg hpro 2
  letI : DistribMulAction Q (ZMod 2) := scalarActionZmodTwo Q
  letI : ContinuousSMul Q (ZMod 2) := scalarActionZmodTwo_continuousSMul Q
  rw [AddMonoidHom.mem_ker]
  change lowerTwoCentralH2Inflation G
    (H2mk Q (ZMod 2) (lowerTwoCentralTransgressionCocycle G hfg hpro chi)) = 0
  rw [show lowerTwoCentralH2Inflation G =
      inf2 ⟨levelMk G 2, continuous_levelMk G 2⟩ (fun _ _ => rfl) from rfl,
    inf2_H2mk]
  apply (QuotientAddGroup.eq_zero_iff _).mpr
  rw [AddSubgroup.mem_addSubgroupOf]
  refine ⟨(lowerTwoCentralKernelPartC1 G hfg hpro chi).1,
    (lowerTwoCentralKernelPartC1 G hfg hpro chi).2, ?_⟩
  exact (lowerTwoCentralTransgression_inflated_eq_dOne G hfg hpro chi).symm

/-- The canonical Schreier transgression with codomain restricted to the inflation kernel. -/
noncomputable def lowerTwoCentralTransgression
    (hfg : IsTopologicallyFinGen G) (hpro : IsProP 2 G) :
    letI : DistribMulAction G (ZMod 2) := scalarActionZmodTwo G
    letI : ContinuousSMul G (ZMod 2) := scalarActionZmodTwo_continuousSMul G
    let Q := levelQuot G 2
    letI : DiscreteTopology Q := discreteTopology_levelQuot G hfg hpro 2
    letI : DistribMulAction Q (ZMod 2) := scalarActionZmodTwo Q
    letI : ContinuousSMul Q (ZMod 2) := scalarActionZmodTwo_continuousSMul Q
    (Additive (zLayer G 2) →+ ZMod 2) →+
      ↥(lowerTwoCentralH2Inflation G).ker := by
  letI : DistribMulAction G (ZMod 2) := scalarActionZmodTwo G
  letI : ContinuousSMul G (ZMod 2) := scalarActionZmodTwo_continuousSMul G
  let Q := levelQuot G 2
  letI : DiscreteTopology Q := discreteTopology_levelQuot G hfg hpro 2
  letI : DistribMulAction Q (ZMod 2) := scalarActionZmodTwo Q
  letI : ContinuousSMul Q (ZMod 2) := scalarActionZmodTwo_continuousSMul Q
  exact (lowerTwoCentralTransgressionH2 G hfg hpro).codRestrict
    (lowerTwoCentralH2Inflation G).ker
    (lowerTwoCentralTransgressionH2_mem_inflationKernel G hfg hpro)

/-- The explicit transgression has trivial kernel.  The proof is the low-degree exactness
argument at cochain level: a coboundary downstairs, subtracted from the kernel-part cochain
upstairs, is a continuous character of `G`; every such character kills `lambda_2`. -/
theorem lowerTwoCentralTransgression_eq_zero_only
    (hfg : IsTopologicallyFinGen G) (hpro : IsProP 2 G)
    (chi : Additive (zLayer G 2) →+ ZMod 2)
    (hzero :
      letI : DistribMulAction G (ZMod 2) := scalarActionZmodTwo G
      letI : ContinuousSMul G (ZMod 2) := scalarActionZmodTwo_continuousSMul G
      let Q := levelQuot G 2
      letI : DiscreteTopology Q := discreteTopology_levelQuot G hfg hpro 2
      letI : DistribMulAction Q (ZMod 2) := scalarActionZmodTwo Q
      letI : ContinuousSMul Q (ZMod 2) := scalarActionZmodTwo_continuousSMul Q
      lowerTwoCentralTransgression G hfg hpro chi = 0) :
    chi = 0 := by
  letI : DistribMulAction G (ZMod 2) := scalarActionZmodTwo G
  letI : ContinuousSMul G (ZMod 2) := scalarActionZmodTwo_continuousSMul G
  let Q := levelQuot G 2
  letI : DiscreteTopology Q := discreteTopology_levelQuot G hfg hpro 2
  letI : DistribMulAction Q (ZMod 2) := scalarActionZmodTwo Q
  letI : ContinuousSMul Q (ZMod 2) := scalarActionZmodTwo_continuousSMul Q
  have hclass : lowerTwoCentralTransgressionH2 G hfg hpro chi = 0 :=
    congrArg Subtype.val hzero
  change H2mk Q (ZMod 2) (lowerTwoCentralTransgressionCocycle G hfg hpro chi) = 0 at hclass
  have hcob := (QuotientAddGroup.eq_zero_iff
    (lowerTwoCentralTransgressionCocycle G hfg hpro chi)).mp hclass
  rw [AddSubgroup.mem_addSubgroupOf] at hcob
  obtain ⟨psi, hpsi, hpsi_eq⟩ := hcob
  let b := lowerTwoCentralKernelPartC1 G hfg hpro chi
  let a : G → ZMod 2 := fun g => b.1 g - psi (levelMk G 2 g)
  have ha_cont : Continuous a :=
    b.2.sub (hpsi.comp (continuous_levelMk G 2))
  have ha_mul : ∀ g h : G, a (g * h) = a g + a h := by
    intro g h
    have hb := congrFun
      (lowerTwoCentralTransgression_inflated_eq_dOne G hfg hpro chi) (g, h)
    have hp := congrFun hpsi_eq (levelMk G 2 g, levelMk G 2 h)
    change chi (Additive.ofMul
        (lowerTwoCentralSectionDefect G (levelMk G 2 g) (levelMk G 2 h))) =
      b.1 h - b.1 (g * h) + b.1 g at hb
    change psi (levelMk G 2 h) - psi (levelMk G 2 (g * h)) + psi (levelMk G 2 g) =
      chi (Additive.ofMul
        (lowerTwoCentralSectionDefect G (levelMk G 2 g) (levelMk G 2 h))) at hp
    have hbmul : b.1 (g * h) = b.1 g + b.1 h -
        chi (Additive.ofMul
          (lowerTwoCentralSectionDefect G (levelMk G 2 g) (levelMk G 2 h))) := by
      rw [hb]
      abel
    have hpmul : psi (levelMk G 2 (g * h)) =
        psi (levelMk G 2 g) + psi (levelMk G 2 h) -
          chi (Additive.ofMul
            (lowerTwoCentralSectionDefect G (levelMk G 2 g) (levelMk G 2 h))) := by
      rw [← hp]
      abel
    dsimp [a]
    rw [hbmul, hpmul]
    abel
  let za : Z1 G (ZMod 2) :=
    ⟨a, (mem_Z1_iff_of_trivial (scalarActionZmodTwo_triv G)).mpr ⟨ha_cont, ha_mul⟩⟩
  have hpsi_one : psi 1 = 0 := by
    have ha_one := Z1_apply_one za
    change b.1 1 - psi 1 = 0 at ha_one
    simpa [b, lowerTwoCentralKernelPartC1] using ha_one
  let c : ContinuousMonoidHom G (Multiplicative (ZMod 2)) := Count.homEquivZ1.symm za
  apply AddMonoidHom.ext
  intro z
  obtain ⟨g, hg, hgz⟩ := z.2
  have hcg : c g = 1 := MonoidHom.mem_ker.mp
    (twoCentralSeries_two_le_continuousCharacter_ker c hg)
  have hazero : za.1 g = 0 := by
    change Multiplicative.ofAdd (za.1 g) = 1 at hcg
    apply Multiplicative.ofAdd.injective
    simpa using hcg
  have hq : levelMk G 2 g = 1 := (QuotientGroup.eq_one_iff g).mpr hg
  have hkernel : Additive.ofMul (lowerTwoCentralKernelPart G g) = z := by
    apply Additive.toMul.injective
    change lowerTwoCentralKernelPart G g = Additive.toMul z
    apply Subtype.ext
    rw [lowerTwoCentralKernelPart_coe_of_mem G hg]
    exact hgz
  have hag : za.1 g = chi z := by
    change b.1 g - psi (levelMk G 2 g) = chi z
    rw [hq, hpsi_one, sub_zero]
    change chi (Additive.ofMul (lowerTwoCentralKernelPart G g)) = chi z
    rw [hkernel]
  change chi z = 0
  rw [← hag, hazero]

/-- Injectivity half of the five-term kernel identification, now unconditional. -/
theorem lowerTwoCentralTransgression_injective
    (hfg : IsTopologicallyFinGen G) (hpro : IsProP 2 G) :
    letI : DistribMulAction G (ZMod 2) := scalarActionZmodTwo G
    letI : ContinuousSMul G (ZMod 2) := scalarActionZmodTwo_continuousSMul G
    let Q := levelQuot G 2
    letI : DiscreteTopology Q := discreteTopology_levelQuot G hfg hpro 2
    letI : DistribMulAction Q (ZMod 2) := scalarActionZmodTwo Q
    letI : ContinuousSMul Q (ZMod 2) := scalarActionZmodTwo_continuousSMul Q
    Function.Injective (lowerTwoCentralTransgression G hfg hpro) := by
  letI : DistribMulAction G (ZMod 2) := scalarActionZmodTwo G
  letI : ContinuousSMul G (ZMod 2) := scalarActionZmodTwo_continuousSMul G
  let Q := levelQuot G 2
  letI : DiscreteTopology Q := discreteTopology_levelQuot G hfg hpro 2
  letI : DistribMulAction Q (ZMod 2) := scalarActionZmodTwo Q
  letI : ContinuousSMul Q (ZMod 2) := scalarActionZmodTwo_continuousSMul Q
  dsimp only
  intro chi psi heq
  apply sub_eq_zero.mp
  apply lowerTwoCentralTransgression_eq_zero_only G hfg hpro (chi - psi)
  rw [map_sub, heq, sub_self]

/-- A primitive for an inflated cocycle restricts to a character of `lambda_2`, invariant
under ambient conjugation and therefore descending to `lambda_2/lambda_3`.  This is the
well-definedness core of five-term surjectivity. -/
theorem exists_lowerTwoCentralLayerCharacter_of_inflation_coboundary
    (z :
      let Q := levelQuot G 2
      letI : DistribMulAction Q (ZMod 2) := scalarActionZmodTwo Q
      letI : ContinuousSMul Q (ZMod 2) := scalarActionZmodTwo_continuousSMul Q
      Z2 Q (ZMod 2))
    (b :
      letI : DistribMulAction G (ZMod 2) := scalarActionZmodTwo G
      letI : ContinuousSMul G (ZMod 2) := scalarActionZmodTwo_continuousSMul G
      C1 G (ZMod 2))
    (hdb :
      letI : DistribMulAction G (ZMod 2) := scalarActionZmodTwo G
      letI : ContinuousSMul G (ZMod 2) := scalarActionZmodTwo_continuousSMul G
      let Q := levelQuot G 2
      letI : DistribMulAction Q (ZMod 2) := scalarActionZmodTwo Q
      letI : ContinuousSMul Q (ZMod 2) := scalarActionZmodTwo_continuousSMul Q
      dOne G (ZMod 2) b.1 =
        (Z2comap ⟨levelMk G 2, continuous_levelMk G 2⟩
          (AddMonoidHom.id (ZMod 2)) continuous_id (fun _ _ => rfl) z).1) :
    ∃ chi : Additive (zLayer G 2) →+ ZMod 2,
      ∀ n : twoCentralSeries G 2,
        chi (Additive.ofMul
          ⟨levelMk G 3 n.1, ⟨n.1, n.2, rfl⟩⟩) = b.1 n.1 - b.1 1 := by
  letI : DistribMulAction G (ZMod 2) := scalarActionZmodTwo G
  letI : ContinuousSMul G (ZMod 2) := scalarActionZmodTwo_continuousSMul G
  let Q := levelQuot G 2
  letI : DistribMulAction Q (ZMod 2) := scalarActionZmodTwo Q
  letI : ContinuousSMul Q (ZMod 2) := scalarActionZmodTwo_continuousSMul Q
  let N := twoCentralSeries G 2
  have hb_one : b.1 1 = z.1 (1, 1) := by
    have h := congrFun hdb (1, 1)
    simpa [dOne, Z2comap] using h
  let cN : ContinuousMonoidHom N (Multiplicative (ZMod 2)) :=
    { toFun := fun n => Multiplicative.ofAdd (b.1 n.1 - b.1 1)
      map_one' := by simp
      map_mul' := by
        intro n m
        apply Multiplicative.ofAdd.injective
        change b.1 (n.1 * m.1) - b.1 1 =
          (b.1 n.1 - b.1 1) + (b.1 m.1 - b.1 1)
        have hnq : levelMk G 2 n.1 = 1 := (QuotientGroup.eq_one_iff n.1).mpr n.2
        have hmq : levelMk G 2 m.1 = 1 := (QuotientGroup.eq_one_iff m.1).mpr m.2
        have hd : b.1 m.1 - b.1 (n.1 * m.1) + b.1 n.1 = z.1 (1, 1) := by
          have hd' := congrFun hdb (n.1, m.1)
          dsimp only [dOne, AddMonoidHom.coe_mk, Z2comap, AddMonoidHom.id_apply] at hd'
          change n.1 • b.1 m.1 - b.1 (n.1 * m.1) + b.1 n.1 =
            z.1 (levelMk G 2 n.1, levelMk G 2 m.1) at hd'
          rw [scalarActionZmodTwo_triv G, hnq, hmq] at hd'
          simpa using hd'
        rw [hb_one, ← hd]
        abel
      continuous_toFun := by
        change Continuous fun n : N => b.1 n.1 - b.1 1
        exact (b.2.comp continuous_subtype_val).sub continuous_const }
  have hz_right (q : Q) : z.1 (q, 1) = z.1 (1, 1) := by
    have hz := (mem_Z2_iff.mp z.2).2 q 1 1
    rw [scalarActionZmodTwo_triv Q] at hz
    have hz' : z.1 (1, 1) + z.1 (q, 1) = z.1 (q, 1) + z.1 (q, 1) := by
      simpa using hz
    exact (add_right_cancel hz').symm
  have hcN_conj (g : G) (n : N) :
      cN ⟨g * n.1 * g⁻¹, by
        exact (twoCentralSeries_normal G 2).conj_mem n.1 n.2 g⟩ = cN n := by
    apply Multiplicative.ofAdd.injective
    change b.1 (g * n.1 * g⁻¹) - b.1 1 = b.1 n.1 - b.1 1
    have hnq : levelMk G 2 n.1 = 1 := (QuotientGroup.eq_one_iff n.1).mpr n.2
    have hgn : b.1 n.1 - b.1 (g * n.1) + b.1 g = z.1 (levelMk G 2 g, 1) := by
      have h := congrFun hdb (g, n.1)
      dsimp only [dOne, AddMonoidHom.coe_mk, Z2comap, AddMonoidHom.id_apply] at h
      change g • b.1 n.1 - b.1 (g * n.1) + b.1 g =
        z.1 (levelMk G 2 g, levelMk G 2 n.1) at h
      rw [scalarActionZmodTwo_triv G, hnq] at h
      simpa using h
    have hstep : b.1 g⁻¹ - b.1 (g * n.1 * g⁻¹) + b.1 (g * n.1) =
        z.1 (levelMk G 2 g, (levelMk G 2 g)⁻¹) := by
      have h := congrFun hdb (g * n.1, g⁻¹)
      dsimp only [dOne, AddMonoidHom.coe_mk, Z2comap, AddMonoidHom.id_apply] at h
      change (g * n.1) • b.1 g⁻¹ - b.1 (g * n.1 * g⁻¹) + b.1 (g * n.1) =
        z.1 (levelMk G 2 (g * n.1), levelMk G 2 g⁻¹) at h
      rw [scalarActionZmodTwo_triv G, map_mul, hnq, mul_one, map_inv] at h
      simpa using h
    have hgg : b.1 g⁻¹ - b.1 1 + b.1 g =
        z.1 (levelMk G 2 g, (levelMk G 2 g)⁻¹) := by
      have h := congrFun hdb (g, g⁻¹)
      dsimp only [dOne, AddMonoidHom.coe_mk, Z2comap, AddMonoidHom.id_apply] at h
      change g • b.1 g⁻¹ - b.1 (g * g⁻¹) + b.1 g =
        z.1 (levelMk G 2 g, levelMk G 2 g⁻¹) at h
      rw [scalarActionZmodTwo_triv G] at h
      simpa using h
    have hgn' : b.1 (g * n.1) = b.1 n.1 + b.1 g - b.1 1 := by
      rw [hb_one, ← hz_right (levelMk G 2 g), ← hgn]
      abel
    have hconj' : b.1 (g * n.1 * g⁻¹) =
        b.1 g⁻¹ + b.1 (g * n.1) -
          z.1 (levelMk G 2 g, (levelMk G 2 g)⁻¹) := by
      rw [eq_sub_iff_add_eq, ← hstep]
      abel
    rw [hconj', ← hgg, hgn']
    abel
  let K : Subgroup G := cN.toMonoidHom.ker.map N.subtype
  have hK_closed : IsClosed (K : Set G) := by
    have hker_closed : IsClosed (cN.toMonoidHom.ker : Set N) := by
      have hset : (cN.toMonoidHom.ker : Set N) = cN ⁻¹' {1} := by
        ext n
        simp [MonoidHom.mem_ker]
      rw [hset]
      exact isClosed_singleton.preimage cN.continuous_toFun
    have hset : (K : Set G) = Subtype.val '' (cN.toMonoidHom.ker : Set N) := by
      ext g
      simp [K]
    rw [hset]
    exact (isClosed_twoCentralSeries G 2).isClosedEmbedding_subtypeVal.isClosedMap _ hker_closed
  have hsucc : twoCentralSucc N ≤ K := by
    apply Subgroup.topologicalClosure_minimal
    · apply sup_le
      · refine (Subgroup.closure_le K).mpr ?_
        rintro _ ⟨n, hn, rfl⟩
        refine ⟨⟨n ^ 2, N.pow_mem hn 2⟩, ?_, rfl⟩
        apply MonoidHom.mem_ker.mpr
        change cN.toMonoidHom ((⟨n, hn⟩ : N) ^ 2) = 1
        rw [map_pow]
        apply Multiplicative.toAdd.injective
        rw [toAdd_pow, toAdd_one, two_nsmul, Count.zmod2_add_self]
      · rw [Subgroup.commutator_le]
        intro n hn g _hg
        let nn : N := ⟨n, hn⟩
        let ng : N := ⟨g * n⁻¹ * g⁻¹,
          (twoCentralSeries_normal G 2).conj_mem n⁻¹ (N.inv_mem hn) g⟩
        have hcommN : ⁅n, g⁆ ∈ N := (Subgroup.commutator_le_left N ⊤)
          (Subgroup.commutator_mem_commutator hn (Subgroup.mem_top g))
        refine ⟨⟨⁅n, g⁆, hcommN⟩, ?_, rfl⟩
        apply MonoidHom.mem_ker.mpr
        have hdecomp : (⟨⁅n, g⁆,
            hcommN⟩ : N) = nn * ng := by
          apply Subtype.ext
          change ⁅n, g⁆ = n * (g * n⁻¹ * g⁻¹)
          rw [commutatorElement_def]
          group
        rw [hdecomp, map_mul]
        change cN nn * cN ⟨g * (nn⁻¹).1 * g⁻¹, _⟩ = 1
        rw [hcN_conj g nn⁻¹, map_inv, mul_inv_cancel]
    · exact hK_closed
  have hthree_le : twoCentralSeries G 3 ≤ K := by
    rw [twoCentralSeries_succ G (by omega)]
    exact hsucc
  let layerMk : N →* zLayer G 2 :=
    { toFun := fun n => ⟨levelMk G 3 n.1, ⟨n.1, n.2, rfl⟩⟩
      map_one' := Subtype.ext (map_one (levelMk G 3))
      map_mul' := fun n m => Subtype.ext (map_mul (levelMk G 3) n.1 m.1) }
  have hlayer_surj : Function.Surjective layerMk := by
    intro x
    obtain ⟨g, hg, hgx⟩ := x.2
    exact ⟨⟨g, hg⟩, Subtype.ext hgx⟩
  have hker : layerMk.ker ≤ cN.toMonoidHom.ker := by
    intro n hn
    have hn3 : n.1 ∈ twoCentralSeries G 3 := by
      apply (QuotientGroup.eq_one_iff n.1).mp
      exact congrArg Subtype.val (MonoidHom.mem_ker.mp hn)
    obtain ⟨m, hm, hmn⟩ := hthree_le hn3
    have hmval : m.1 = n.1 := by simpa using hmn
    have hmker : cN m = 1 := MonoidHom.mem_ker.mp hm
    have hmn : m = n := Subtype.ext hmval
    rw [← hmn]
    exact hmker
  let cL : zLayer G 2 →* Multiplicative (ZMod 2) :=
    MonoidHom.liftOfSurjective layerMk hlayer_surj ⟨cN.toMonoidHom, hker⟩
  let chi : Additive (zLayer G 2) →+ ZMod 2 :=
    { toFun := fun x => Multiplicative.toAdd (cL x.toMul)
      map_zero' := congrArg Multiplicative.toAdd (map_one cL)
      map_add' := fun x y => congrArg Multiplicative.toAdd (map_mul cL x.toMul y.toMul) }
  refine ⟨chi, ?_⟩
  intro n
  change Multiplicative.toAdd (cL (layerMk n)) = b.1 n.1 - b.1 1
  rw [show cL (layerMk n) = cN n from by simp [cL]]
  rfl

/-- The character descended from an inflation primitive transgresses back to the original
cohomology class.  The comparison cochain is `q ↦ b (section q)`. -/
theorem lowerTwoCentralTransgressionH2_eq_of_primitive
    (hfg : IsTopologicallyFinGen G) (hpro : IsProP 2 G)
    (z :
      let Q := levelQuot G 2
      letI : DistribMulAction Q (ZMod 2) := scalarActionZmodTwo Q
      letI : ContinuousSMul Q (ZMod 2) := scalarActionZmodTwo_continuousSMul Q
      Z2 Q (ZMod 2))
    (b :
      letI : DistribMulAction G (ZMod 2) := scalarActionZmodTwo G
      letI : ContinuousSMul G (ZMod 2) := scalarActionZmodTwo_continuousSMul G
      C1 G (ZMod 2))
    (hdb :
      letI : DistribMulAction G (ZMod 2) := scalarActionZmodTwo G
      letI : ContinuousSMul G (ZMod 2) := scalarActionZmodTwo_continuousSMul G
      let Q := levelQuot G 2
      letI : DistribMulAction Q (ZMod 2) := scalarActionZmodTwo Q
      letI : ContinuousSMul Q (ZMod 2) := scalarActionZmodTwo_continuousSMul Q
      dOne G (ZMod 2) b.1 =
        (Z2comap ⟨levelMk G 2, continuous_levelMk G 2⟩
          (AddMonoidHom.id (ZMod 2)) continuous_id (fun _ _ => rfl) z).1)
    (chi : Additive (zLayer G 2) →+ ZMod 2)
    (hchi : ∀ n : twoCentralSeries G 2,
      chi (Additive.ofMul
        ⟨levelMk G 3 n.1, ⟨n.1, n.2, rfl⟩⟩) = b.1 n.1 - b.1 1) :
    letI : DistribMulAction G (ZMod 2) := scalarActionZmodTwo G
    letI : ContinuousSMul G (ZMod 2) := scalarActionZmodTwo_continuousSMul G
    let Q := levelQuot G 2
    letI : DiscreteTopology Q := discreteTopology_levelQuot G hfg hpro 2
    letI : DistribMulAction Q (ZMod 2) := scalarActionZmodTwo Q
    letI : ContinuousSMul Q (ZMod 2) := scalarActionZmodTwo_continuousSMul Q
    lowerTwoCentralTransgressionH2 G hfg hpro chi = H2mk Q (ZMod 2) z := by
  letI : DistribMulAction G (ZMod 2) := scalarActionZmodTwo G
  letI : ContinuousSMul G (ZMod 2) := scalarActionZmodTwo_continuousSMul G
  let Q := levelQuot G 2
  letI : DiscreteTopology Q := discreteTopology_levelQuot G hfg hpro 2
  letI : DistribMulAction Q (ZMod 2) := scalarActionZmodTwo Q
  letI : ContinuousSMul Q (ZMod 2) := scalarActionZmodTwo_continuousSMul Q
  let psi : C1 Q (ZMod 2) :=
    ⟨fun q => b.1 (lowerTwoCentralSection G q), continuous_of_discreteTopology⟩
  have hd_mem : dOne Q (ZMod 2) psi.1 ∈ B2 Q (ZMod 2) := by
    exact ⟨psi.1, psi.2, rfl⟩
  let dz : Z2 Q (ZMod 2) :=
    ⟨dOne Q (ZMod 2) psi.1, B2_le_Z2 hd_mem⟩
  have hcochain : lowerTwoCentralTransgressionCocycle G hfg hpro chi = z + dz := by
    apply Subtype.ext
    funext p
    obtain ⟨q, r⟩ := p
    let sq := lowerTwoCentralSection G q
    let sr := lowerTwoCentralSection G r
    let sqr := lowerTwoCentralSection G (q * r)
    let nraw := sq * sr * sqr⁻¹
    have hnraw : nraw ∈ twoCentralSeries G 2 := by
      apply (QuotientGroup.eq_one_iff nraw).mp
      change levelMk G 2 nraw = 1
      dsimp [nraw, sq, sr, sqr]
      rw [map_mul, map_mul, map_inv, levelMk_lowerTwoCentralSection,
        levelMk_lowerTwoCentralSection, levelMk_lowerTwoCentralSection]
      group
    let n : twoCentralSeries G 2 := ⟨nraw, hnraw⟩
    have hchi_defect :
        chi (Additive.ofMul (lowerTwoCentralSectionDefect G q r)) =
          b.1 nraw - b.1 1 := by
      simpa [lowerTwoCentralSectionDefect, n, nraw, sq, sr, sqr] using hchi n
    have hone : z.1 (1, q * r) = b.1 1 := by
      have h := congrFun hdb (1, sqr)
      dsimp only [dOne, AddMonoidHom.coe_mk, Z2comap, AddMonoidHom.id_apply] at h
      change (1 : G) • b.1 sqr - b.1 (1 * sqr) + b.1 1 =
        z.1 (levelMk G 2 1, levelMk G 2 sqr) at h
      rw [scalarActionZmodTwo_triv G, one_mul, map_one,
        show levelMk G 2 sqr = q * r from levelMk_lowerTwoCentralSection G (q * r)] at h
      simpa using h.symm
    have hnprod : nraw * sqr = sq * sr := by
      dsimp [nraw]
      group
    have hnprimitive : b.1 nraw - b.1 1 = b.1 (sq * sr) - b.1 sqr := by
      have h := congrFun hdb (nraw, sqr)
      dsimp only [dOne, AddMonoidHom.coe_mk, Z2comap, AddMonoidHom.id_apply] at h
      change nraw • b.1 sqr - b.1 (nraw * sqr) + b.1 nraw =
        z.1 (levelMk G 2 nraw, levelMk G 2 sqr) at h
      have hnq : levelMk G 2 nraw = 1 :=
        (QuotientGroup.eq_one_iff nraw).mpr hnraw
      rw [scalarActionZmodTwo_triv G, hnq,
        show levelMk G 2 sqr = q * r from levelMk_lowerTwoCentralSection G (q * r),
        hone, hnprod] at h
      rw [← h]
      abel
    have hqr : z.1 (q, r) = b.1 sr - b.1 (sq * sr) + b.1 sq := by
      have h := congrFun hdb (sq, sr)
      dsimp only [dOne, AddMonoidHom.coe_mk, Z2comap, AddMonoidHom.id_apply] at h
      change sq • b.1 sr - b.1 (sq * sr) + b.1 sq =
        z.1 (levelMk G 2 sq, levelMk G 2 sr) at h
      rw [scalarActionZmodTwo_triv G,
        show levelMk G 2 sq = q from levelMk_lowerTwoCentralSection G q,
        show levelMk G 2 sr = r from levelMk_lowerTwoCentralSection G r] at h
      exact h.symm
    change chi (Additive.ofMul (lowerTwoCentralSectionDefect G q r)) =
      z.1 (q, r) + (q • psi.1 r - psi.1 (q * r) + psi.1 q)
    rw [scalarActionZmodTwo_triv Q, hchi_defect, hnprimitive, hqr]
    dsimp [psi, sq, sr, sqr]
    ring_nf
    simp [show (2 : ZMod 2) = 0 by decide, CharTwo.neg_eq]
  change H2mk Q (ZMod 2) (lowerTwoCentralTransgressionCocycle G hfg hpro chi) =
    H2mk Q (ZMod 2) z
  rw [hcochain, map_add]
  have hdz_zero : H2mk Q (ZMod 2) dz = 0 := by
    apply (QuotientAddGroup.eq_zero_iff _).mpr
    rw [AddSubgroup.mem_addSubgroupOf]
    exact hd_mem
  rw [hdz_zero, add_zero]

/-- The remaining five-term theorem is precisely bijectivity of the explicit transgression. -/
def LowerTwoCentralTransgressionBijective
    (hfg : IsTopologicallyFinGen G) (hpro : IsProP 2 G) : Prop :=
  letI : DistribMulAction G (ZMod 2) := scalarActionZmodTwo G
  letI : ContinuousSMul G (ZMod 2) := scalarActionZmodTwo_continuousSMul G
  let Q := levelQuot G 2
  letI : DiscreteTopology Q := discreteTopology_levelQuot G hfg hpro 2
  letI : DistribMulAction Q (ZMod 2) := scalarActionZmodTwo Q
  letI : ContinuousSMul Q (ZMod 2) := scalarActionZmodTwo_continuousSMul Q
  Function.Bijective (lowerTwoCentralTransgression G hfg hpro)

/-- Bijectivity of the explicit transgression supplies the earlier equivalence-shaped
five-term kernel-duality interface. -/
theorem lowerTwoCentralFiveTermKernelDuality_of_transgressionBijective
    (hfg : IsTopologicallyFinGen G) (hpro : IsProP 2 G)
    (hbij : LowerTwoCentralTransgressionBijective G hfg hpro) :
    LowerTwoCentralFiveTermKernelDuality G := by
  letI : DistribMulAction G (ZMod 2) := scalarActionZmodTwo G
  letI : ContinuousSMul G (ZMod 2) := scalarActionZmodTwo_continuousSMul G
  let Q := levelQuot G 2
  letI : DiscreteTopology Q := discreteTopology_levelQuot G hfg hpro 2
  letI : DistribMulAction Q (ZMod 2) := scalarActionZmodTwo Q
  letI : ContinuousSMul Q (ZMod 2) := scalarActionZmodTwo_continuousSMul Q
  exact ⟨AddEquiv.ofBijective (lowerTwoCentralTransgression G hfg hpro) hbij⟩

end Cocycle

#print axioms lowerTwoCentralSectionDefect_cocycle
#print axioms lowerTwoCentralKernelPart_mul
#print axioms lowerTwoCentralTransgression_inflated_eq_dOne
#print axioms lowerTwoCentralTransgressionH2_mem_inflationKernel
#print axioms lowerTwoCentralTransgression_injective
#print axioms exists_lowerTwoCentralLayerCharacter_of_inflation_coboundary
#print axioms lowerTwoCentralTransgressionH2_eq_of_primitive
#print axioms lowerTwoCentralFiveTermKernelDuality_of_transgressionBijective

end


end GQ2.Dyadic.LSquare
