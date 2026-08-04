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

section Defect

variable (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- The chosen set-theoretic section of `G -> G/lambda_2`. -/
def lowerTwoCentralSection (q : levelQuot G 2) : G :=
  Quotient.out q

@[simp] theorem levelMk_lowerTwoCentralSection (q : levelQuot G 2) :
    levelMk G 2 (lowerTwoCentralSection G q) = q :=
  Quotient.out_eq q

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
#print axioms lowerTwoCentralFiveTermKernelDuality_of_transgressionBijective

end


end GQ2.Dyadic.LSquare
