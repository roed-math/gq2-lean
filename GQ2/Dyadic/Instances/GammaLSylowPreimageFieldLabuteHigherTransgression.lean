/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using OpenAI Codex
-/
import GQ2.Dyadic.Instances.GammaLSylowPreimageFieldLabuteTransgression

/-!
# Schreier transgression at every lower two-central stage

This is the stage-`k` version of the explicit construction previously available only for
`lambda_2/lambda_3`.  A section of `G → G/lambda_k` has a factor set in `lambda_k`; projecting
it to `zLayer G k` and evaluating by a mod-two character gives a two-cocycle on
`levelQuot G k`.  For `k ≥ 2`, the resulting cohomology map is injective.
-/

namespace GQ2.Dyadic.LSquare

noncomputable section

open GQ2 GQ2.Roe.Labute ContCoh
open scoped commutatorElement

section Defect

variable (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- The chosen set-theoretic section of `G → G/lambda_k`. -/
def lowerTwoCentralSectionAt (k : ℕ) (q : levelQuot G k) : G := by
  classical
  exact if q = 1 then 1 else Quotient.out q

@[simp] theorem lowerTwoCentralSectionAt_one (k : ℕ) :
    lowerTwoCentralSectionAt G k 1 = 1 := by
  simp [lowerTwoCentralSectionAt]

@[simp] theorem levelMk_lowerTwoCentralSectionAt (k : ℕ) (q : levelQuot G k) :
    levelMk G k (lowerTwoCentralSectionAt G k q) = q := by
  classical
  by_cases hq : q = 1
  · simp [lowerTwoCentralSectionAt, hq]
  · rw [lowerTwoCentralSectionAt, if_neg hq]
    exact QuotientGroup.out_eq' q

/-- The stage-`k` section factor set, projected to `lambda_k/lambda_(k+1)`. -/
def lowerTwoCentralSectionDefectAt (k : ℕ)
    (q r : levelQuot G k) : zLayer G k := by
  let x := lowerTwoCentralSectionAt G k q * lowerTwoCentralSectionAt G k r *
    (lowerTwoCentralSectionAt G k (q * r))⁻¹
  have hx : x ∈ twoCentralSeries G k := by
    apply (QuotientGroup.eq_one_iff x).mp
    change levelMk G k x = 1
    dsimp [x]
    rw [map_mul, map_mul, map_inv, levelMk_lowerTwoCentralSectionAt,
      levelMk_lowerTwoCentralSectionAt, levelMk_lowerTwoCentralSectionAt]
    group
  exact ⟨levelMk G (k + 1) x, ⟨x, hx, rfl⟩⟩

/-- The stage-`k` kernel component of an ambient element. -/
def lowerTwoCentralKernelPartAt (k : ℕ) (g : G) : zLayer G k := by
  let x := g * (lowerTwoCentralSectionAt G k (levelMk G k g))⁻¹
  have hx : x ∈ twoCentralSeries G k := by
    apply (QuotientGroup.eq_one_iff x).mp
    change levelMk G k x = 1
    dsimp [x]
    rw [map_mul, map_inv, levelMk_lowerTwoCentralSectionAt]
    group
  exact ⟨levelMk G (k + 1) x, ⟨x, hx, rfl⟩⟩

@[simp] theorem lowerTwoCentralSectionDefectAt_one_one (k : ℕ) :
    lowerTwoCentralSectionDefectAt G k 1 1 = 1 := by
  apply Subtype.ext
  simp [lowerTwoCentralSectionDefectAt]

@[simp] theorem lowerTwoCentralKernelPartAt_one (k : ℕ) :
    lowerTwoCentralKernelPartAt G k 1 = 1 := by
  apply Subtype.ext
  simp [lowerTwoCentralKernelPartAt]

/-- On `lambda_k`, the kernel component is the element itself modulo `lambda_(k+1)`. -/
theorem lowerTwoCentralKernelPartAt_coe_of_mem (k : ℕ)
    {g : G} (hg : g ∈ twoCentralSeries G k) :
    (lowerTwoCentralKernelPartAt G k g).1 = levelMk G (k + 1) g := by
  have hq : levelMk G k g = 1 := (QuotientGroup.eq_one_iff g).mpr hg
  dsimp [lowerTwoCentralKernelPartAt]
  rw [hq, lowerTwoCentralSectionAt_one]
  simp

/-- The stage-`k` factor set satisfies the additive cocycle identity. -/
theorem lowerTwoCentralSectionDefectAt_cocycle (k : ℕ)
    (g h l : levelQuot G k) :
    Additive.ofMul (lowerTwoCentralSectionDefectAt G k h l) +
        Additive.ofMul (lowerTwoCentralSectionDefectAt G k g (h * l)) =
      Additive.ofMul (lowerTwoCentralSectionDefectAt G k (g * h) l) +
        Additive.ofMul (lowerTwoCentralSectionDefectAt G k g h) := by
  apply Additive.toMul.injective
  apply Subtype.ext
  change (lowerTwoCentralSectionDefectAt G k h l).1 *
      (lowerTwoCentralSectionDefectAt G k g (h * l)).1 =
    (lowerTwoCentralSectionDefectAt G k (g * h) l).1 *
      (lowerTwoCentralSectionDefectAt G k g h).1
  have hcentral := Subgroup.mem_center_iff.mp
    (zLayer_le_center G k (lowerTwoCentralSectionDefectAt G k h l).2)
    (levelMk G (k + 1) (lowerTwoCentralSectionAt G k g))
  have hright := Subgroup.mem_center_iff.mp
    (zLayer_le_center G k (lowerTwoCentralSectionDefectAt G k (g * h) l).2)
    (lowerTwoCentralSectionDefectAt G k g h).1
  change levelMk G (k + 1) (lowerTwoCentralSectionAt G k g) *
      levelMk G (k + 1) (lowerTwoCentralSectionAt G k h *
        lowerTwoCentralSectionAt G k l *
        (lowerTwoCentralSectionAt G k (h * l))⁻¹) =
    levelMk G (k + 1) (lowerTwoCentralSectionAt G k h *
        lowerTwoCentralSectionAt G k l *
        (lowerTwoCentralSectionAt G k (h * l))⁻¹) *
      levelMk G (k + 1) (lowerTwoCentralSectionAt G k g) at hcentral
  dsimp [lowerTwoCentralSectionDefectAt] at hright ⊢
  simp only [map_mul, map_inv] at hcentral hright ⊢
  let sg := levelMk G (k + 1) (lowerTwoCentralSectionAt G k g)
  let sh := levelMk G (k + 1) (lowerTwoCentralSectionAt G k h)
  let sl := levelMk G (k + 1) (lowerTwoCentralSectionAt G k l)
  let shl := levelMk G (k + 1) (lowerTwoCentralSectionAt G k (h * l))
  let sgh := levelMk G (k + 1) (lowerTwoCentralSectionAt G k (g * h))
  let sghl := levelMk G (k + 1) (lowerTwoCentralSectionAt G k (g * h * l))
  change sg * (sh * sl * shl⁻¹) = (sh * sl * shl⁻¹) * sg at hcentral
  change (sg * sh * sgh⁻¹) * (sgh * sl * sghl⁻¹) =
    (sgh * sl * sghl⁻¹) * (sg * sh * sgh⁻¹) at hright
  rw [← mul_assoc g h l]
  change (sh * sl * shl⁻¹) * (sg * shl * sghl⁻¹) =
    (sgh * sl * sghl⁻¹) * (sg * sh * sgh⁻¹)
  calc
    (sh * sl * shl⁻¹) * (sg * shl * sghl⁻¹) =
        ((sh * sl * shl⁻¹) * sg) * shl * sghl⁻¹ := by group
    _ = (sg * (sh * sl * shl⁻¹)) * shl * sghl⁻¹ := by rw [← hcentral]
    _ = (sg * sh * sgh⁻¹) * (sgh * sl * sghl⁻¹) := by group
    _ = (sgh * sl * sghl⁻¹) * (sg * sh * sgh⁻¹) := hright

/-- Kernel components multiply by the stage-`k` section factor set. -/
theorem lowerTwoCentralKernelPartAt_mul (k : ℕ) (g h : G) :
    Additive.ofMul (lowerTwoCentralKernelPartAt G k (g * h)) =
      Additive.ofMul (lowerTwoCentralKernelPartAt G k g) +
        Additive.ofMul (lowerTwoCentralKernelPartAt G k h) +
          Additive.ofMul
            (lowerTwoCentralSectionDefectAt G k (levelMk G k g) (levelMk G k h)) := by
  apply Additive.toMul.injective
  apply Subtype.ext
  change (lowerTwoCentralKernelPartAt G k (g * h)).1 =
    (lowerTwoCentralKernelPartAt G k g).1 *
      (lowerTwoCentralKernelPartAt G k h).1 *
        (lowerTwoCentralSectionDefectAt G k (levelMk G k g) (levelMk G k h)).1
  have hcentral := Subgroup.mem_center_iff.mp
    (zLayer_le_center G k (lowerTwoCentralKernelPartAt G k h).2)
    (levelMk G (k + 1) (lowerTwoCentralSectionAt G k (levelMk G k g)))
  change levelMk G (k + 1) (lowerTwoCentralSectionAt G k (levelMk G k g)) *
      levelMk G (k + 1) (h * (lowerTwoCentralSectionAt G k (levelMk G k h))⁻¹) =
    levelMk G (k + 1) (h * (lowerTwoCentralSectionAt G k (levelMk G k h))⁻¹) *
      levelMk G (k + 1) (lowerTwoCentralSectionAt G k (levelMk G k g)) at hcentral
  dsimp [lowerTwoCentralKernelPartAt, lowerTwoCentralSectionDefectAt]
  simp only [map_mul, map_inv] at hcentral ⊢
  let gg := levelMk G (k + 1) g
  let hh := levelMk G (k + 1) h
  let sg := levelMk G (k + 1) (lowerTwoCentralSectionAt G k (levelMk G k g))
  let sh := levelMk G (k + 1) (lowerTwoCentralSectionAt G k (levelMk G k h))
  let sgh := levelMk G (k + 1)
    (lowerTwoCentralSectionAt G k (levelMk G k g * levelMk G k h))
  change sg * (hh * sh⁻¹) = (hh * sh⁻¹) * sg at hcentral
  change gg * hh * sgh⁻¹ = gg * sg⁻¹ * (hh * sh⁻¹) * (sg * sh * sgh⁻¹)
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

/-- Evaluating the stage-`k` section factor set gives a continuous mod-two two-cocycle. -/
noncomputable def lowerTwoCentralTransgressionCocycleAt (k : ℕ)
    (hfg : IsTopologicallyFinGen G) (hpro : IsProP 2 G)
    (chi : Additive (zLayer G k) →+ ZMod 2) :
    let Q := levelQuot G k
    letI : DiscreteTopology Q := discreteTopology_levelQuot G hfg hpro k
    letI : DistribMulAction Q (ZMod 2) := scalarActionZmodTwo Q
    letI : ContinuousSMul Q (ZMod 2) := scalarActionZmodTwo_continuousSMul Q
    Z2 Q (ZMod 2) := by
  let Q := levelQuot G k
  letI : DiscreteTopology Q := discreteTopology_levelQuot G hfg hpro k
  letI : DistribMulAction Q (ZMod 2) := scalarActionZmodTwo Q
  letI : ContinuousSMul Q (ZMod 2) := scalarActionZmodTwo_continuousSMul Q
  refine ⟨fun p => chi (Additive.ofMul (lowerTwoCentralSectionDefectAt G k p.1 p.2)), ?_⟩
  apply mem_Z2_iff.mpr
  refine ⟨continuous_of_discreteTopology, ?_⟩
  intro g h l
  change chi (Additive.ofMul (lowerTwoCentralSectionDefectAt G k h l)) +
      chi (Additive.ofMul (lowerTwoCentralSectionDefectAt G k g (h * l))) =
    chi (Additive.ofMul (lowerTwoCentralSectionDefectAt G k (g * h) l)) +
      chi (Additive.ofMul (lowerTwoCentralSectionDefectAt G k g h))
  rw [← map_add, lowerTwoCentralSectionDefectAt_cocycle, map_add]

/-- The stage-`k` section-defect construction is additive in the layer character. -/
noncomputable def lowerTwoCentralTransgressionZ2At (k : ℕ)
    (hfg : IsTopologicallyFinGen G) (hpro : IsProP 2 G) :
    let Q := levelQuot G k
    letI : DiscreteTopology Q := discreteTopology_levelQuot G hfg hpro k
    letI : DistribMulAction Q (ZMod 2) := scalarActionZmodTwo Q
    letI : ContinuousSMul Q (ZMod 2) := scalarActionZmodTwo_continuousSMul Q
    (Additive (zLayer G k) →+ ZMod 2) →+ Z2 Q (ZMod 2) := by
  let Q := levelQuot G k
  letI : DiscreteTopology Q := discreteTopology_levelQuot G hfg hpro k
  letI : DistribMulAction Q (ZMod 2) := scalarActionZmodTwo Q
  letI : ContinuousSMul Q (ZMod 2) := scalarActionZmodTwo_continuousSMul Q
  exact
    { toFun := lowerTwoCentralTransgressionCocycleAt G k hfg hpro
      map_zero' := by
        apply Subtype.ext
        funext p
        rfl
      map_add' := by
        intro chi psi
        apply Subtype.ext
        funext p
        rfl }

/-- The cohomology-level stage-`k` transgression. -/
noncomputable def lowerTwoCentralTransgressionH2At (k : ℕ)
    (hfg : IsTopologicallyFinGen G) (hpro : IsProP 2 G) :
    let Q := levelQuot G k
    letI : DiscreteTopology Q := discreteTopology_levelQuot G hfg hpro k
    letI : DistribMulAction Q (ZMod 2) := scalarActionZmodTwo Q
    letI : ContinuousSMul Q (ZMod 2) := scalarActionZmodTwo_continuousSMul Q
    (Additive (zLayer G k) →+ ZMod 2) →+ H2 Q (ZMod 2) := by
  let Q := levelQuot G k
  letI : DiscreteTopology Q := discreteTopology_levelQuot G hfg hpro k
  letI : DistribMulAction Q (ZMod 2) := scalarActionZmodTwo Q
  letI : ContinuousSMul Q (ZMod 2) := scalarActionZmodTwo_continuousSMul Q
  exact (H2mk Q (ZMod 2)).comp (lowerTwoCentralTransgressionZ2At G k hfg hpro)

/-- The continuous kernel-component cochain at stage `k`. -/
noncomputable def lowerTwoCentralKernelPartC1At (k : ℕ)
    (hfg : IsTopologicallyFinGen G) (hpro : IsProP 2 G)
    (chi : Additive (zLayer G k) →+ ZMod 2) :
    letI : DistribMulAction G (ZMod 2) := scalarActionZmodTwo G
    letI : ContinuousSMul G (ZMod 2) := scalarActionZmodTwo_continuousSMul G
    C1 G (ZMod 2) := by
  letI : DistribMulAction G (ZMod 2) := scalarActionZmodTwo G
  letI : ContinuousSMul G (ZMod 2) := scalarActionZmodTwo_continuousSMul G
  let Q := levelQuot G k
  let Qnext := levelQuot G (k + 1)
  letI : DiscreteTopology Q := discreteTopology_levelQuot G hfg hpro k
  letI : DiscreteTopology Qnext := discreteTopology_levelQuot G hfg hpro (k + 1)
  refine ⟨fun g => chi (Additive.ofMul (lowerTwoCentralKernelPartAt G k g)), ?_⟩
  have hsection : Continuous (lowerTwoCentralSectionAt G k : Q → G) :=
    continuous_of_discreteTopology
  have hraw : Continuous fun g : G =>
      levelMk G (k + 1)
        (g * (lowerTwoCentralSectionAt G k (levelMk G k g))⁻¹) :=
    (continuous_levelMk G (k + 1)).comp
      (continuous_id.mul ((hsection.comp (continuous_levelMk G k)).inv))
  have hpart : Continuous (lowerTwoCentralKernelPartAt G k : G → zLayer G k) := by
    exact Continuous.subtype_mk hraw _
  have hchi : Continuous fun z : zLayer G k => chi (Additive.ofMul z) :=
    continuous_of_discreteTopology
  exact hchi.comp hpart

/-- The inflated stage-`k` transgression cocycle is the coboundary of the kernel-component
cochain. -/
theorem lowerTwoCentralTransgressionAt_inflated_eq_dOne (k : ℕ)
    (hfg : IsTopologicallyFinGen G) (hpro : IsProP 2 G)
    (chi : Additive (zLayer G k) →+ ZMod 2) :
    letI : DistribMulAction G (ZMod 2) := scalarActionZmodTwo G
    letI : ContinuousSMul G (ZMod 2) := scalarActionZmodTwo_continuousSMul G
    let Q := levelQuot G k
    letI : DiscreteTopology Q := discreteTopology_levelQuot G hfg hpro k
    letI : DistribMulAction Q (ZMod 2) := scalarActionZmodTwo Q
    letI : ContinuousSMul Q (ZMod 2) := scalarActionZmodTwo_continuousSMul Q
    (Z2comap ⟨levelMk G k, continuous_levelMk G k⟩ (AddMonoidHom.id (ZMod 2))
      continuous_id (fun _ _ => rfl)
      (lowerTwoCentralTransgressionCocycleAt G k hfg hpro chi)).1 =
        dOne G (ZMod 2) (lowerTwoCentralKernelPartC1At G k hfg hpro chi).1 := by
  letI : DistribMulAction G (ZMod 2) := scalarActionZmodTwo G
  letI : ContinuousSMul G (ZMod 2) := scalarActionZmodTwo_continuousSMul G
  let Q := levelQuot G k
  letI : DiscreteTopology Q := discreteTopology_levelQuot G hfg hpro k
  letI : DistribMulAction Q (ZMod 2) := scalarActionZmodTwo Q
  letI : ContinuousSMul Q (ZMod 2) := scalarActionZmodTwo_continuousSMul Q
  funext p
  obtain ⟨g, l⟩ := p
  have hmul := congrArg chi (lowerTwoCentralKernelPartAt_mul G k g l)
  rw [map_add, map_add] at hmul
  change chi (Additive.ofMul
      (lowerTwoCentralSectionDefectAt G k (levelMk G k g) (levelMk G k l))) =
    chi (Additive.ofMul (lowerTwoCentralKernelPartAt G k l)) -
      chi (Additive.ofMul (lowerTwoCentralKernelPartAt G k (g * l))) +
        chi (Additive.ofMul (lowerTwoCentralKernelPartAt G k g))
  have hneg (x : ZMod 2) : x = -x := by
    exact eq_neg_of_add_eq_zero_left (CharTwo.add_self_eq_zero x)
  calc
    chi (Additive.ofMul
        (lowerTwoCentralSectionDefectAt G k (levelMk G k g) (levelMk G k l))) =
        -chi (Additive.ofMul
          (lowerTwoCentralSectionDefectAt G k (levelMk G k g) (levelMk G k l))) := hneg _
    _ = chi (Additive.ofMul (lowerTwoCentralKernelPartAt G k l)) -
          (chi (Additive.ofMul (lowerTwoCentralKernelPartAt G k g)) +
            chi (Additive.ofMul (lowerTwoCentralKernelPartAt G k l)) +
              chi (Additive.ofMul
                (lowerTwoCentralSectionDefectAt G k
                  (levelMk G k g) (levelMk G k l)))) +
            chi (Additive.ofMul (lowerTwoCentralKernelPartAt G k g)) := by abel
    _ = chi (Additive.ofMul (lowerTwoCentralKernelPartAt G k l)) -
          chi (Additive.ofMul (lowerTwoCentralKernelPartAt G k (g * l))) +
            chi (Additive.ofMul (lowerTwoCentralKernelPartAt G k g)) := by rw [hmul]

/-- At every stage `k ≥ 2`, only the zero layer character transgresses to the zero
cohomology class. -/
theorem lowerTwoCentralTransgressionH2At_eq_zero_only (k : ℕ) (hk : 2 ≤ k)
    (hfg : IsTopologicallyFinGen G) (hpro : IsProP 2 G)
    (chi : Additive (zLayer G k) →+ ZMod 2)
    (hzero :
      let Q := levelQuot G k
      letI : DiscreteTopology Q := discreteTopology_levelQuot G hfg hpro k
      letI : DistribMulAction Q (ZMod 2) := scalarActionZmodTwo Q
      letI : ContinuousSMul Q (ZMod 2) := scalarActionZmodTwo_continuousSMul Q
      lowerTwoCentralTransgressionH2At G k hfg hpro chi = 0) :
    chi = 0 := by
  letI : DistribMulAction G (ZMod 2) := scalarActionZmodTwo G
  letI : ContinuousSMul G (ZMod 2) := scalarActionZmodTwo_continuousSMul G
  let Q := levelQuot G k
  letI : DiscreteTopology Q := discreteTopology_levelQuot G hfg hpro k
  letI : DistribMulAction Q (ZMod 2) := scalarActionZmodTwo Q
  letI : ContinuousSMul Q (ZMod 2) := scalarActionZmodTwo_continuousSMul Q
  change H2mk Q (ZMod 2)
    (lowerTwoCentralTransgressionCocycleAt G k hfg hpro chi) = 0 at hzero
  have hcob := (QuotientAddGroup.eq_zero_iff
    (lowerTwoCentralTransgressionCocycleAt G k hfg hpro chi)).mp hzero
  rw [AddSubgroup.mem_addSubgroupOf] at hcob
  obtain ⟨psi, hpsi, hpsi_eq⟩ := hcob
  let b := lowerTwoCentralKernelPartC1At G k hfg hpro chi
  let a : G → ZMod 2 := fun g => b.1 g - psi (levelMk G k g)
  have ha_cont : Continuous a :=
    b.2.sub (hpsi.comp (continuous_levelMk G k))
  have ha_mul : ∀ g l : G, a (g * l) = a g + a l := by
    intro g l
    have hb := congrFun
      (lowerTwoCentralTransgressionAt_inflated_eq_dOne G k hfg hpro chi) (g, l)
    have hp := congrFun hpsi_eq (levelMk G k g, levelMk G k l)
    change chi (Additive.ofMul
        (lowerTwoCentralSectionDefectAt G k (levelMk G k g) (levelMk G k l))) =
      b.1 l - b.1 (g * l) + b.1 g at hb
    change psi (levelMk G k l) - psi (levelMk G k (g * l)) + psi (levelMk G k g) =
      chi (Additive.ofMul
        (lowerTwoCentralSectionDefectAt G k (levelMk G k g) (levelMk G k l))) at hp
    have hbmul : b.1 (g * l) = b.1 g + b.1 l -
        chi (Additive.ofMul
          (lowerTwoCentralSectionDefectAt G k (levelMk G k g) (levelMk G k l))) := by
      rw [hb]
      abel
    have hpmul : psi (levelMk G k (g * l)) =
        psi (levelMk G k g) + psi (levelMk G k l) -
          chi (Additive.ofMul
            (lowerTwoCentralSectionDefectAt G k (levelMk G k g) (levelMk G k l))) := by
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
    simpa [b, lowerTwoCentralKernelPartC1At] using ha_one
  let c : ContinuousMonoidHom G (Multiplicative (ZMod 2)) := Count.homEquivZ1.symm za
  apply AddMonoidHom.ext
  intro z
  obtain ⟨g, hg, hgz⟩ := z.2
  have hg2 : g ∈ twoCentralSeries G 2 := twoCentralSeries_antitone G hk hg
  have hcg : c g = 1 := MonoidHom.mem_ker.mp
    (twoCentralSeries_two_le_continuousCharacter_ker c hg2)
  have hazero : za.1 g = 0 := by
    change Multiplicative.ofAdd (za.1 g) = 1 at hcg
    apply Multiplicative.ofAdd.injective
    simpa using hcg
  have hq : levelMk G k g = 1 := (QuotientGroup.eq_one_iff g).mpr hg
  have hkernel : Additive.ofMul (lowerTwoCentralKernelPartAt G k g) = z := by
    apply Additive.toMul.injective
    change lowerTwoCentralKernelPartAt G k g = Additive.toMul z
    apply Subtype.ext
    rw [lowerTwoCentralKernelPartAt_coe_of_mem G k hg]
    exact hgz
  have hag : za.1 g = chi z := by
    change b.1 g - psi (levelMk G k g) = chi z
    rw [hq, hpsi_one, sub_zero]
    change chi (Additive.ofMul (lowerTwoCentralKernelPartAt G k g)) = chi z
    rw [hkernel]
  change chi z = 0
  rw [← hag, hazero]

/-- The stage-`k` transgression into `H²(levelQuot G k, F₂)` is injective for `k ≥ 2`. -/
theorem lowerTwoCentralTransgressionH2At_injective (k : ℕ) (hk : 2 ≤ k)
    (hfg : IsTopologicallyFinGen G) (hpro : IsProP 2 G) :
    let Q := levelQuot G k
    letI : DiscreteTopology Q := discreteTopology_levelQuot G hfg hpro k
    letI : DistribMulAction Q (ZMod 2) := scalarActionZmodTwo Q
    letI : ContinuousSMul Q (ZMod 2) := scalarActionZmodTwo_continuousSMul Q
    Function.Injective (lowerTwoCentralTransgressionH2At G k hfg hpro) := by
  let Q := levelQuot G k
  letI : DiscreteTopology Q := discreteTopology_levelQuot G hfg hpro k
  letI : DistribMulAction Q (ZMod 2) := scalarActionZmodTwo Q
  letI : ContinuousSMul Q (ZMod 2) := scalarActionZmodTwo_continuousSMul Q
  dsimp only
  intro chi psi heq
  apply sub_eq_zero.mp
  apply lowerTwoCentralTransgressionH2At_eq_zero_only G k hk hfg hpro (chi - psi)
  rw [map_sub, heq, sub_self]

/-- Canonical degree-two inflation from the stage-`k` quotient. -/
noncomputable def lowerTwoCentralH2InflationAt (k : ℕ) :
    letI : DistribMulAction G (ZMod 2) := scalarActionZmodTwo G
    letI : ContinuousSMul G (ZMod 2) := scalarActionZmodTwo_continuousSMul G
    let Q := levelQuot G k
    letI : DistribMulAction Q (ZMod 2) := scalarActionZmodTwo Q
    letI : ContinuousSMul Q (ZMod 2) := scalarActionZmodTwo_continuousSMul Q
    H2 Q (ZMod 2) →+ H2 G (ZMod 2) := by
  letI : DistribMulAction G (ZMod 2) := scalarActionZmodTwo G
  letI : ContinuousSMul G (ZMod 2) := scalarActionZmodTwo_continuousSMul G
  let Q := levelQuot G k
  letI : DistribMulAction Q (ZMod 2) := scalarActionZmodTwo Q
  letI : ContinuousSMul Q (ZMod 2) := scalarActionZmodTwo_continuousSMul Q
  exact inf2 ⟨levelMk G k, continuous_levelMk G k⟩ (fun _ _ => rfl)

/-- Every stage-`k` transgression class lies in the kernel of inflation to `G`. -/
theorem lowerTwoCentralTransgressionH2At_mem_inflationKernel (k : ℕ)
    (hfg : IsTopologicallyFinGen G) (hpro : IsProP 2 G)
    (chi : Additive (zLayer G k) →+ ZMod 2) :
    letI : DistribMulAction G (ZMod 2) := scalarActionZmodTwo G
    letI : ContinuousSMul G (ZMod 2) := scalarActionZmodTwo_continuousSMul G
    let Q := levelQuot G k
    letI : DiscreteTopology Q := discreteTopology_levelQuot G hfg hpro k
    letI : DistribMulAction Q (ZMod 2) := scalarActionZmodTwo Q
    letI : ContinuousSMul Q (ZMod 2) := scalarActionZmodTwo_continuousSMul Q
    lowerTwoCentralTransgressionH2At G k hfg hpro chi ∈
      (lowerTwoCentralH2InflationAt G k).ker := by
  letI : DistribMulAction G (ZMod 2) := scalarActionZmodTwo G
  letI : ContinuousSMul G (ZMod 2) := scalarActionZmodTwo_continuousSMul G
  let Q := levelQuot G k
  letI : DiscreteTopology Q := discreteTopology_levelQuot G hfg hpro k
  letI : DistribMulAction Q (ZMod 2) := scalarActionZmodTwo Q
  letI : ContinuousSMul Q (ZMod 2) := scalarActionZmodTwo_continuousSMul Q
  rw [AddMonoidHom.mem_ker]
  change lowerTwoCentralH2InflationAt G k
    (H2mk Q (ZMod 2) (lowerTwoCentralTransgressionCocycleAt G k hfg hpro chi)) = 0
  rw [show lowerTwoCentralH2InflationAt G k =
      inf2 ⟨levelMk G k, continuous_levelMk G k⟩ (fun _ _ => rfl) from rfl,
    inf2_H2mk]
  apply (QuotientAddGroup.eq_zero_iff _).mpr
  rw [AddSubgroup.mem_addSubgroupOf]
  refine ⟨(lowerTwoCentralKernelPartC1At G k hfg hpro chi).1,
    (lowerTwoCentralKernelPartC1At G k hfg hpro chi).2, ?_⟩
  exact (lowerTwoCentralTransgressionAt_inflated_eq_dOne G k hfg hpro chi).symm

/-- The stage-`k` transgression with codomain restricted to the inflation kernel. -/
noncomputable def lowerTwoCentralTransgressionAt (k : ℕ)
    (hfg : IsTopologicallyFinGen G) (hpro : IsProP 2 G) :
    letI : DistribMulAction G (ZMod 2) := scalarActionZmodTwo G
    letI : ContinuousSMul G (ZMod 2) := scalarActionZmodTwo_continuousSMul G
    let Q := levelQuot G k
    letI : DiscreteTopology Q := discreteTopology_levelQuot G hfg hpro k
    letI : DistribMulAction Q (ZMod 2) := scalarActionZmodTwo Q
    letI : ContinuousSMul Q (ZMod 2) := scalarActionZmodTwo_continuousSMul Q
    (Additive (zLayer G k) →+ ZMod 2) →+
      ↥(lowerTwoCentralH2InflationAt G k).ker := by
  letI : DistribMulAction G (ZMod 2) := scalarActionZmodTwo G
  letI : ContinuousSMul G (ZMod 2) := scalarActionZmodTwo_continuousSMul G
  let Q := levelQuot G k
  letI : DiscreteTopology Q := discreteTopology_levelQuot G hfg hpro k
  letI : DistribMulAction Q (ZMod 2) := scalarActionZmodTwo Q
  letI : ContinuousSMul Q (ZMod 2) := scalarActionZmodTwo_continuousSMul Q
  exact (lowerTwoCentralTransgressionH2At G k hfg hpro).codRestrict
    (lowerTwoCentralH2InflationAt G k).ker
    (lowerTwoCentralTransgressionH2At_mem_inflationKernel G k hfg hpro)

/-- The restricted stage-`k` transgression is injective for `k ≥ 2`. -/
theorem lowerTwoCentralTransgressionAt_injective (k : ℕ) (hk : 2 ≤ k)
    (hfg : IsTopologicallyFinGen G) (hpro : IsProP 2 G) :
    letI : DistribMulAction G (ZMod 2) := scalarActionZmodTwo G
    letI : ContinuousSMul G (ZMod 2) := scalarActionZmodTwo_continuousSMul G
    let Q := levelQuot G k
    letI : DiscreteTopology Q := discreteTopology_levelQuot G hfg hpro k
    letI : DistribMulAction Q (ZMod 2) := scalarActionZmodTwo Q
    letI : ContinuousSMul Q (ZMod 2) := scalarActionZmodTwo_continuousSMul Q
    Function.Injective (lowerTwoCentralTransgressionAt G k hfg hpro) := by
  letI : DistribMulAction G (ZMod 2) := scalarActionZmodTwo G
  letI : ContinuousSMul G (ZMod 2) := scalarActionZmodTwo_continuousSMul G
  let Q := levelQuot G k
  letI : DiscreteTopology Q := discreteTopology_levelQuot G hfg hpro k
  letI : DistribMulAction Q (ZMod 2) := scalarActionZmodTwo Q
  letI : ContinuousSMul Q (ZMod 2) := scalarActionZmodTwo_continuousSMul Q
  dsimp only
  intro chi psi heq
  apply lowerTwoCentralTransgressionH2At_injective G k hk hfg hpro
  exact congrArg Subtype.val heq

/-- A primitive for a stage-`k` inflated cocycle restricts to a conjugation-invariant
character of `lambda_k`, hence descends to `zLayer G k`. -/
theorem exists_lowerTwoCentralLayerCharacterAt_of_inflation_coboundary
    (k : ℕ) (hk : 2 ≤ k)
    (z :
      let Q := levelQuot G k
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
      let Q := levelQuot G k
      letI : DistribMulAction Q (ZMod 2) := scalarActionZmodTwo Q
      letI : ContinuousSMul Q (ZMod 2) := scalarActionZmodTwo_continuousSMul Q
      dOne G (ZMod 2) b.1 =
        (Z2comap ⟨levelMk G k, continuous_levelMk G k⟩
          (AddMonoidHom.id (ZMod 2)) continuous_id (fun _ _ => rfl) z).1) :
    ∃ chi : Additive (zLayer G k) →+ ZMod 2,
      ∀ n : twoCentralSeries G k,
        chi (Additive.ofMul
          ⟨levelMk G (k + 1) n.1, ⟨n.1, n.2, rfl⟩⟩) = b.1 n.1 - b.1 1 := by
  letI : DistribMulAction G (ZMod 2) := scalarActionZmodTwo G
  letI : ContinuousSMul G (ZMod 2) := scalarActionZmodTwo_continuousSMul G
  let Q := levelQuot G k
  letI : DistribMulAction Q (ZMod 2) := scalarActionZmodTwo Q
  letI : ContinuousSMul Q (ZMod 2) := scalarActionZmodTwo_continuousSMul Q
  let N := twoCentralSeries G k
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
        have hnq : levelMk G k n.1 = 1 := (QuotientGroup.eq_one_iff n.1).mpr n.2
        have hmq : levelMk G k m.1 = 1 := (QuotientGroup.eq_one_iff m.1).mpr m.2
        have hd : b.1 m.1 - b.1 (n.1 * m.1) + b.1 n.1 = z.1 (1, 1) := by
          have hd' := congrFun hdb (n.1, m.1)
          dsimp only [dOne, AddMonoidHom.coe_mk, Z2comap, AddMonoidHom.id_apply] at hd'
          change n.1 • b.1 m.1 - b.1 (n.1 * m.1) + b.1 n.1 =
            z.1 (levelMk G k n.1, levelMk G k m.1) at hd'
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
        exact (twoCentralSeries_normal G k).conj_mem n.1 n.2 g⟩ = cN n := by
    apply Multiplicative.ofAdd.injective
    change b.1 (g * n.1 * g⁻¹) - b.1 1 = b.1 n.1 - b.1 1
    have hnq : levelMk G k n.1 = 1 := (QuotientGroup.eq_one_iff n.1).mpr n.2
    have hgn : b.1 n.1 - b.1 (g * n.1) + b.1 g = z.1 (levelMk G k g, 1) := by
      have h := congrFun hdb (g, n.1)
      dsimp only [dOne, AddMonoidHom.coe_mk, Z2comap, AddMonoidHom.id_apply] at h
      change g • b.1 n.1 - b.1 (g * n.1) + b.1 g =
        z.1 (levelMk G k g, levelMk G k n.1) at h
      rw [scalarActionZmodTwo_triv G, hnq] at h
      simpa using h
    have hstep : b.1 g⁻¹ - b.1 (g * n.1 * g⁻¹) + b.1 (g * n.1) =
        z.1 (levelMk G k g, (levelMk G k g)⁻¹) := by
      have h := congrFun hdb (g * n.1, g⁻¹)
      dsimp only [dOne, AddMonoidHom.coe_mk, Z2comap, AddMonoidHom.id_apply] at h
      change (g * n.1) • b.1 g⁻¹ - b.1 (g * n.1 * g⁻¹) + b.1 (g * n.1) =
        z.1 (levelMk G k (g * n.1), levelMk G k g⁻¹) at h
      rw [scalarActionZmodTwo_triv G, map_mul, hnq, mul_one, map_inv] at h
      simpa using h
    have hgg : b.1 g⁻¹ - b.1 1 + b.1 g =
        z.1 (levelMk G k g, (levelMk G k g)⁻¹) := by
      have h := congrFun hdb (g, g⁻¹)
      dsimp only [dOne, AddMonoidHom.coe_mk, Z2comap, AddMonoidHom.id_apply] at h
      change g • b.1 g⁻¹ - b.1 (g * g⁻¹) + b.1 g =
        z.1 (levelMk G k g, levelMk G k g⁻¹) at h
      rw [scalarActionZmodTwo_triv G] at h
      simpa using h
    have hgn' : b.1 (g * n.1) = b.1 n.1 + b.1 g - b.1 1 := by
      rw [hb_one, ← hz_right (levelMk G k g), ← hgn]
      abel
    have hconj' : b.1 (g * n.1 * g⁻¹) =
        b.1 g⁻¹ + b.1 (g * n.1) -
          z.1 (levelMk G k g, (levelMk G k g)⁻¹) := by
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
    exact (isClosed_twoCentralSeries G k).isClosedEmbedding_subtypeVal.isClosedMap _ hker_closed
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
          (twoCentralSeries_normal G k).conj_mem n⁻¹ (N.inv_mem hn) g⟩
        have hcommN : ⁅n, g⁆ ∈ N := (Subgroup.commutator_le_left N ⊤)
          (Subgroup.commutator_mem_commutator hn (Subgroup.mem_top g))
        refine ⟨⟨⁅n, g⁆, hcommN⟩, ?_, rfl⟩
        apply MonoidHom.mem_ker.mpr
        have hdecomp : (⟨⁅n, g⁆, hcommN⟩ : N) = nn * ng := by
          apply Subtype.ext
          change ⁅n, g⁆ = n * (g * n⁻¹ * g⁻¹)
          rw [commutatorElement_def]
          group
        rw [hdecomp, map_mul]
        change cN nn * cN ⟨g * (nn⁻¹).1 * g⁻¹, _⟩ = 1
        rw [hcN_conj g nn⁻¹, map_inv, mul_inv_cancel]
    · exact hK_closed
  have hnext_le : twoCentralSeries G (k + 1) ≤ K := by
    rw [twoCentralSeries_succ G (by omega)]
    exact hsucc
  let layerMk : N →* zLayer G k :=
    { toFun := fun n => ⟨levelMk G (k + 1) n.1, ⟨n.1, n.2, rfl⟩⟩
      map_one' := Subtype.ext (map_one (levelMk G (k + 1)))
      map_mul' := fun n m => Subtype.ext (map_mul (levelMk G (k + 1)) n.1 m.1) }
  have hlayer_surj : Function.Surjective layerMk := by
    intro x
    obtain ⟨g, hg, hgx⟩ := x.2
    exact ⟨⟨g, hg⟩, Subtype.ext hgx⟩
  have hker : layerMk.ker ≤ cN.toMonoidHom.ker := by
    intro n hn
    have hnnext : n.1 ∈ twoCentralSeries G (k + 1) := by
      apply (QuotientGroup.eq_one_iff n.1).mp
      exact congrArg Subtype.val (MonoidHom.mem_ker.mp hn)
    obtain ⟨m, hm, hmn⟩ := hnext_le hnnext
    have hmval : m.1 = n.1 := by simpa using hmn
    have hmker : cN m = 1 := MonoidHom.mem_ker.mp hm
    have hmn : m = n := Subtype.ext hmval
    rw [← hmn]
    exact hmker
  let cL : zLayer G k →* Multiplicative (ZMod 2) :=
    MonoidHom.liftOfSurjective layerMk hlayer_surj ⟨cN.toMonoidHom, hker⟩
  let chi : Additive (zLayer G k) →+ ZMod 2 :=
    { toFun := fun x => Multiplicative.toAdd (cL x.toMul)
      map_zero' := congrArg Multiplicative.toAdd (map_one cL)
      map_add' := fun x y => congrArg Multiplicative.toAdd (map_mul cL x.toMul y.toMul) }
  refine ⟨chi, ?_⟩
  intro n
  change Multiplicative.toAdd (cL (layerMk n)) = b.1 n.1 - b.1 1
  rw [show cL (layerMk n) = cN n from by simp [cL]]
  rfl

/-- The character reconstructed from an inflation primitive transgresses back to the
original stage-`k` cohomology class. -/
theorem lowerTwoCentralTransgressionH2At_eq_of_primitive
    (k : ℕ) (hfg : IsTopologicallyFinGen G) (hpro : IsProP 2 G)
    (z :
      let Q := levelQuot G k
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
      let Q := levelQuot G k
      letI : DistribMulAction Q (ZMod 2) := scalarActionZmodTwo Q
      letI : ContinuousSMul Q (ZMod 2) := scalarActionZmodTwo_continuousSMul Q
      dOne G (ZMod 2) b.1 =
        (Z2comap ⟨levelMk G k, continuous_levelMk G k⟩
          (AddMonoidHom.id (ZMod 2)) continuous_id (fun _ _ => rfl) z).1)
    (chi : Additive (zLayer G k) →+ ZMod 2)
    (hchi : ∀ n : twoCentralSeries G k,
      chi (Additive.ofMul
        ⟨levelMk G (k + 1) n.1, ⟨n.1, n.2, rfl⟩⟩) = b.1 n.1 - b.1 1) :
    letI : DistribMulAction G (ZMod 2) := scalarActionZmodTwo G
    letI : ContinuousSMul G (ZMod 2) := scalarActionZmodTwo_continuousSMul G
    let Q := levelQuot G k
    letI : DiscreteTopology Q := discreteTopology_levelQuot G hfg hpro k
    letI : DistribMulAction Q (ZMod 2) := scalarActionZmodTwo Q
    letI : ContinuousSMul Q (ZMod 2) := scalarActionZmodTwo_continuousSMul Q
    lowerTwoCentralTransgressionH2At G k hfg hpro chi = H2mk Q (ZMod 2) z := by
  letI : DistribMulAction G (ZMod 2) := scalarActionZmodTwo G
  letI : ContinuousSMul G (ZMod 2) := scalarActionZmodTwo_continuousSMul G
  let Q := levelQuot G k
  letI : DiscreteTopology Q := discreteTopology_levelQuot G hfg hpro k
  letI : DistribMulAction Q (ZMod 2) := scalarActionZmodTwo Q
  letI : ContinuousSMul Q (ZMod 2) := scalarActionZmodTwo_continuousSMul Q
  let psi : C1 Q (ZMod 2) :=
    ⟨fun q => b.1 (lowerTwoCentralSectionAt G k q), continuous_of_discreteTopology⟩
  have hd_mem : dOne Q (ZMod 2) psi.1 ∈ B2 Q (ZMod 2) := by
    exact ⟨psi.1, psi.2, rfl⟩
  let dz : Z2 Q (ZMod 2) :=
    ⟨dOne Q (ZMod 2) psi.1, B2_le_Z2 hd_mem⟩
  have hcochain : lowerTwoCentralTransgressionCocycleAt G k hfg hpro chi = z + dz := by
    apply Subtype.ext
    funext p
    obtain ⟨q, r⟩ := p
    let sq := lowerTwoCentralSectionAt G k q
    let sr := lowerTwoCentralSectionAt G k r
    let sqr := lowerTwoCentralSectionAt G k (q * r)
    let nraw := sq * sr * sqr⁻¹
    have hnraw : nraw ∈ twoCentralSeries G k := by
      apply (QuotientGroup.eq_one_iff nraw).mp
      change levelMk G k nraw = 1
      dsimp [nraw, sq, sr, sqr]
      rw [map_mul, map_mul, map_inv, levelMk_lowerTwoCentralSectionAt,
        levelMk_lowerTwoCentralSectionAt, levelMk_lowerTwoCentralSectionAt]
      group
    let n : twoCentralSeries G k := ⟨nraw, hnraw⟩
    have hchi_defect :
        chi (Additive.ofMul (lowerTwoCentralSectionDefectAt G k q r)) =
          b.1 nraw - b.1 1 := by
      simpa [lowerTwoCentralSectionDefectAt, n, nraw, sq, sr, sqr] using hchi n
    have hone : z.1 (1, q * r) = b.1 1 := by
      have h := congrFun hdb (1, sqr)
      dsimp only [dOne, AddMonoidHom.coe_mk, Z2comap, AddMonoidHom.id_apply] at h
      change (1 : G) • b.1 sqr - b.1 (1 * sqr) + b.1 1 =
        z.1 (levelMk G k 1, levelMk G k sqr) at h
      rw [scalarActionZmodTwo_triv G, one_mul, map_one,
        show levelMk G k sqr = q * r from levelMk_lowerTwoCentralSectionAt G k (q * r)] at h
      simpa using h.symm
    have hnprod : nraw * sqr = sq * sr := by
      dsimp [nraw]
      group
    have hnprimitive : b.1 nraw - b.1 1 = b.1 (sq * sr) - b.1 sqr := by
      have h := congrFun hdb (nraw, sqr)
      dsimp only [dOne, AddMonoidHom.coe_mk, Z2comap, AddMonoidHom.id_apply] at h
      change nraw • b.1 sqr - b.1 (nraw * sqr) + b.1 nraw =
        z.1 (levelMk G k nraw, levelMk G k sqr) at h
      have hnq : levelMk G k nraw = 1 :=
        (QuotientGroup.eq_one_iff nraw).mpr hnraw
      rw [scalarActionZmodTwo_triv G, hnq,
        show levelMk G k sqr = q * r from levelMk_lowerTwoCentralSectionAt G k (q * r),
        hone, hnprod] at h
      rw [← h]
      abel
    have hqr : z.1 (q, r) = b.1 sr - b.1 (sq * sr) + b.1 sq := by
      have h := congrFun hdb (sq, sr)
      dsimp only [dOne, AddMonoidHom.coe_mk, Z2comap, AddMonoidHom.id_apply] at h
      change sq • b.1 sr - b.1 (sq * sr) + b.1 sq =
        z.1 (levelMk G k sq, levelMk G k sr) at h
      rw [scalarActionZmodTwo_triv G,
        show levelMk G k sq = q from levelMk_lowerTwoCentralSectionAt G k q,
        show levelMk G k sr = r from levelMk_lowerTwoCentralSectionAt G k r] at h
      exact h.symm
    change chi (Additive.ofMul (lowerTwoCentralSectionDefectAt G k q r)) =
      z.1 (q, r) + (q • psi.1 r - psi.1 (q * r) + psi.1 q)
    rw [scalarActionZmodTwo_triv Q, hchi_defect, hnprimitive, hqr]
    dsimp [psi, sq, sr, sqr]
    ring_nf
    simp [show (2 : ZMod 2) = 0 by decide, CharTwo.neg_eq]
  change H2mk Q (ZMod 2) (lowerTwoCentralTransgressionCocycleAt G k hfg hpro chi) =
    H2mk Q (ZMod 2) z
  rw [hcochain, map_add]
  have hdz_zero : H2mk Q (ZMod 2) dz = 0 := by
    apply (QuotientAddGroup.eq_zero_iff _).mpr
    rw [AddSubgroup.mem_addSubgroupOf]
    exact hd_mem
  rw [hdz_zero, add_zero]

/-- The restricted stage-`k` transgression is surjective onto the inflation kernel. -/
theorem lowerTwoCentralTransgressionAt_surjective (k : ℕ) (hk : 2 ≤ k)
    (hfg : IsTopologicallyFinGen G) (hpro : IsProP 2 G) :
    letI : DistribMulAction G (ZMod 2) := scalarActionZmodTwo G
    letI : ContinuousSMul G (ZMod 2) := scalarActionZmodTwo_continuousSMul G
    let Q := levelQuot G k
    letI : DiscreteTopology Q := discreteTopology_levelQuot G hfg hpro k
    letI : DistribMulAction Q (ZMod 2) := scalarActionZmodTwo Q
    letI : ContinuousSMul Q (ZMod 2) := scalarActionZmodTwo_continuousSMul Q
    Function.Surjective (lowerTwoCentralTransgressionAt G k hfg hpro) := by
  letI : DistribMulAction G (ZMod 2) := scalarActionZmodTwo G
  letI : ContinuousSMul G (ZMod 2) := scalarActionZmodTwo_continuousSMul G
  let Q := levelQuot G k
  letI : DiscreteTopology Q := discreteTopology_levelQuot G hfg hpro k
  letI : DistribMulAction Q (ZMod 2) := scalarActionZmodTwo Q
  letI : ContinuousSMul Q (ZMod 2) := scalarActionZmodTwo_continuousSMul Q
  dsimp only
  intro y
  obtain ⟨z, hz⟩ := H2mk_surjective (G := Q) (M := ZMod 2) y.1
  have hinflated_zero : H2mk G (ZMod 2)
      (Z2comap ⟨levelMk G k, continuous_levelMk G k⟩
        (AddMonoidHom.id (ZMod 2)) continuous_id (fun _ _ => rfl) z) = 0 := by
    rw [← inf2_H2mk]
    change lowerTwoCentralH2InflationAt G k (H2mk Q (ZMod 2) z) = 0
    rw [hz]
    exact AddMonoidHom.mem_ker.mp y.2
  have hcob := (QuotientAddGroup.eq_zero_iff
    (Z2comap ⟨levelMk G k, continuous_levelMk G k⟩
      (AddMonoidHom.id (ZMod 2)) continuous_id (fun _ _ => rfl) z)).mp hinflated_zero
  rw [AddSubgroup.mem_addSubgroupOf] at hcob
  obtain ⟨bfun, hbcont, hbfun⟩ := hcob
  let b : C1 G (ZMod 2) := ⟨bfun, hbcont⟩
  have hdb : dOne G (ZMod 2) b.1 =
      (Z2comap ⟨levelMk G k, continuous_levelMk G k⟩
        (AddMonoidHom.id (ZMod 2)) continuous_id (fun _ _ => rfl) z).1 := by
    exact hbfun
  obtain ⟨chi, hchi⟩ :=
    exists_lowerTwoCentralLayerCharacterAt_of_inflation_coboundary G k hk z b hdb
  refine ⟨chi, Subtype.ext ?_⟩
  change lowerTwoCentralTransgressionH2At G k hfg hpro chi = y.1
  rw [lowerTwoCentralTransgressionH2At_eq_of_primitive G k hfg hpro z b hdb chi hchi, hz]

/-- The generic stage-`k` five-term transgression is bijective for every `k ≥ 2`. -/
theorem lowerTwoCentralTransgressionAt_bijective (k : ℕ) (hk : 2 ≤ k)
    (hfg : IsTopologicallyFinGen G) (hpro : IsProP 2 G) :
    letI : DistribMulAction G (ZMod 2) := scalarActionZmodTwo G
    letI : ContinuousSMul G (ZMod 2) := scalarActionZmodTwo_continuousSMul G
    let Q := levelQuot G k
    letI : DiscreteTopology Q := discreteTopology_levelQuot G hfg hpro k
    letI : DistribMulAction Q (ZMod 2) := scalarActionZmodTwo Q
    letI : ContinuousSMul Q (ZMod 2) := scalarActionZmodTwo_continuousSMul Q
    Function.Bijective (lowerTwoCentralTransgressionAt G k hfg hpro) := by
  letI : DistribMulAction G (ZMod 2) := scalarActionZmodTwo G
  letI : ContinuousSMul G (ZMod 2) := scalarActionZmodTwo_continuousSMul G
  let Q := levelQuot G k
  letI : DiscreteTopology Q := discreteTopology_levelQuot G hfg hpro k
  letI : DistribMulAction Q (ZMod 2) := scalarActionZmodTwo Q
  letI : ContinuousSMul Q (ZMod 2) := scalarActionZmodTwo_continuousSMul Q
  exact ⟨lowerTwoCentralTransgressionAt_injective G k hk hfg hpro,
    lowerTwoCentralTransgressionAt_surjective G k hk hfg hpro⟩

/-- Equivalence form of the generic stage-`k` five-term kernel identification. -/
noncomputable def lowerTwoCentralTransgressionEquivAt (k : ℕ) (hk : 2 ≤ k)
    (hfg : IsTopologicallyFinGen G) (hpro : IsProP 2 G) :
    letI : DistribMulAction G (ZMod 2) := scalarActionZmodTwo G
    letI : ContinuousSMul G (ZMod 2) := scalarActionZmodTwo_continuousSMul G
    let Q := levelQuot G k
    letI : DiscreteTopology Q := discreteTopology_levelQuot G hfg hpro k
    letI : DistribMulAction Q (ZMod 2) := scalarActionZmodTwo Q
    letI : ContinuousSMul Q (ZMod 2) := scalarActionZmodTwo_continuousSMul Q
    (Additive (zLayer G k) →+ ZMod 2) ≃+
      ↥(lowerTwoCentralH2InflationAt G k).ker := by
  letI : DistribMulAction G (ZMod 2) := scalarActionZmodTwo G
  letI : ContinuousSMul G (ZMod 2) := scalarActionZmodTwo_continuousSMul G
  let Q := levelQuot G k
  letI : DiscreteTopology Q := discreteTopology_levelQuot G hfg hpro k
  letI : DistribMulAction Q (ZMod 2) := scalarActionZmodTwo Q
  letI : ContinuousSMul Q (ZMod 2) := scalarActionZmodTwo_continuousSMul Q
  exact AddEquiv.ofBijective (lowerTwoCentralTransgressionAt G k hfg hpro)
    (lowerTwoCentralTransgressionAt_bijective G k hk hfg hpro)

end Cocycle

#print axioms lowerTwoCentralSectionDefectAt_cocycle
#print axioms lowerTwoCentralKernelPartAt_mul
#print axioms lowerTwoCentralTransgressionH2At
#print axioms lowerTwoCentralTransgressionAt_inflated_eq_dOne
#print axioms lowerTwoCentralTransgressionH2At_injective
#print axioms exists_lowerTwoCentralLayerCharacterAt_of_inflation_coboundary
#print axioms lowerTwoCentralTransgressionH2At_eq_of_primitive
#print axioms lowerTwoCentralTransgressionAt_surjective
#print axioms lowerTwoCentralTransgressionAt_bijective
#print axioms lowerTwoCentralTransgressionEquivAt

end


end GQ2.Dyadic.LSquare
