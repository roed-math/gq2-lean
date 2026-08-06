/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Fable-5
-/
import GQ2.Dyadic.Instances.GammaLSylowPreimageFieldLabuteStageKummerParity

/-!
# The cubic neutral damage supply is a theorem: the Jacobi realization

This file discharges the final open input of the odd-degree forward route,
`SqCubicNeutralDamageSupply K h`: at the cubic stage the `2h` flip-damage brackets
`[σ̄², z̄]` lie in the mod-16 neutral shift span, for **every** stage tuple of **every**
finite `K` and every handle count.

The realization is the multi-coordinate one forced by the borderline digit verdict, and it
is digit-free: all four correction entries are single commutators, whose mod-16 cyclotomic
digits vanish because `χ` lands in an abelian group.  Writing `s = σ̄`, `y = x̄₁`,
`z` for the damaged handle letter, and `B = [s, z]`:

* the square collapse (`stageDamage_decomposition` at `k = 3`) rewrites the damage as
  `B² · [B, s]`;
* the twisted slot `x₁` supplies `B² · [B, y]` (its diagonal row), the `x₀` slot supplies
  `[B, s]` and `[[z, y], s]`, and the damaged handle slot itself supplies `[[y, s], z]` —
  a *commutator* head in place of the sharp σ-power head;
* the leftover `[B, y] · [[z, y], s] · [[y, s], z]` is exactly the cyclic Jacobi product
  of `(s, z, y)`, and the **class-three Jacobi identity** (`cubicNeutral_jacobi`) makes it
  vanish in `Q₄`: the Hall–Witt identity collapses because in `Q₄` every double bracket is
  a central involution and `[λ₂, λ₂] = 1`.

The Jacobi identity is the digit-blind span relation invisible to the χ-shadowed
functional calculus — which is why the residual could be neither proven nor refuted there.
With the supply a theorem, the capstone
`nonempty_orientedEquiv_oddDegree_of_cubicNeutralDamage` immediately yields the
**forward presentation theorem** for every odd-degree field
(`nonempty_orientedEquiv_oddDegree`), with no per-`K` input left.
-/

namespace GQ2.Dyadic.LSquare

noncomputable section

open GQ2
open GQ2.Roe.Labute

local notation "ℚ̄₂" => AlgebraicClosure ℚ_[2]

/-! ## The class-three Jacobi identity in `Q₄` -/

section Jacobi

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- Any commutator of two `Q₄`-classes is a depth-`2` modification. -/
private theorem cubicNeutral_commP_mem (x y : levelQuot G (3 + 1)) :
    commP x y ∈ lambdaImage G (3 - 1) (3 + 1) := by
  have hx : x ∈ lambdaImage G 1 (3 + 1) := by rw [lambdaImage_one_eq_top]; trivial
  have hy : y ∈ lambdaImage G 1 (3 + 1) := by rw [lambdaImage_one_eq_top]; trivial
  exact commP_mem_lambdaImage_add hx hy

/-- Conjugation is invisible on a central element (pure group identity). -/
private theorem cubicNeutral_conj_central {H : Type*} [Group H] {u : H}
    (hu : ∀ t : H, u * t = t * u) (g : H) : g⁻¹ * u * g = u := by
  calc g⁻¹ * u * g = g⁻¹ * (u * g) := by group
    _ = g⁻¹ * (g * u) := by rw [hu g]
    _ = u := by group

/-- Inverting the first argument of a bracket with a depth-`2` first argument is invisible
in `Q₄`: the bracket is a central involution. -/
private theorem cubicNeutral_commP_inv_fst {w : levelQuot G (3 + 1)}
    (hw : w ∈ lambdaImage G (3 - 1) (3 + 1)) (z : levelQuot G (3 + 1)) :
    commP w⁻¹ z = commP w z := by
  have hu : commP w z ∈ zLayer G 3 := commP_mem_zLayer 3 le_rfl hw z
  have hid : commP w⁻¹ z = w * (commP w z)⁻¹ * w⁻¹ := by
    simp only [commP]; group
  rw [hid, zLayer_inv_self hu, ← (zLayer_commute hu w).eq, mul_assoc, mul_inv_cancel,
    mul_one]

/-- Inverting the inner argument of a double bracket is invisible in `Q₄`. -/
private theorem cubicNeutral_commP_inv_snd (x y z : levelQuot G (3 + 1)) :
    commP (commP x y⁻¹) z = commP (commP x y) z := by
  have hone : y⁻¹ ∈ lambdaImage G 1 (3 + 1) := by rw [lambdaImage_one_eq_top]; trivial
  have hζ : commP y⁻¹ (commP x y) ∈ zLayer G 3 :=
    commP_mem_lambdaImage_add hone (cubicNeutral_commP_mem x y)
  have hA : commP x y⁻¹ = commP y⁻¹ (commP x y) * (commP x y)⁻¹ := by
    simp only [commP]; group
  rw [hA, commP_central_left (zLayer_commute hζ),
    cubicNeutral_commP_inv_fst (cubicNeutral_commP_mem x y) z]

/-- The Hall–Witt identity in the repo `commP` convention (a free-group identity). -/
private theorem cubicNeutral_hallWitt {H : Type*} [Group H] (a b c : H) :
    b⁻¹ * commP (commP a b⁻¹) c * b * (c⁻¹ * commP (commP b c⁻¹) a * c) *
      (a⁻¹ * commP (commP c a⁻¹) b * a) = 1 := by
  simp only [commP]
  group

/-- **The class-three Jacobi identity.**  In `Q₄` the three cyclic double brackets of any
triple multiply to one: the Hall–Witt conjugates and inner inverses evaporate because
every double bracket is a central involution.  This is the digit-blind span relation that
realizes the flip damage neutrally — invisible to every χ-shadowed functional. -/
theorem cubicNeutral_jacobi (a b c : levelQuot G (3 + 1)) :
    commP (commP a b) c * commP (commP b c) a * commP (commP c a) b = 1 := by
  have h1 : commP (commP a b) c ∈ zLayer G 3 :=
    commP_mem_zLayer 3 le_rfl (cubicNeutral_commP_mem a b) c
  have h2 : commP (commP b c) a ∈ zLayer G 3 :=
    commP_mem_zLayer 3 le_rfl (cubicNeutral_commP_mem b c) a
  have h3 : commP (commP c a) b ∈ zLayer G 3 :=
    commP_mem_zLayer 3 le_rfl (cubicNeutral_commP_mem c a) b
  have hHW := cubicNeutral_hallWitt a b c
  rw [cubicNeutral_commP_inv_snd a b c, cubicNeutral_commP_inv_snd b c a,
    cubicNeutral_commP_inv_snd c a b,
    cubicNeutral_conj_central (fun t ↦ (zLayer_commute h1 t).eq) b,
    cubicNeutral_conj_central (fun t ↦ (zLayer_commute h2 t).eq) c,
    cubicNeutral_conj_central (fun t ↦ (zLayer_commute h3 t).eq) a] at hHW
  exact hHW

/-- **The damage-word identity**: the literal shift word of the four-coordinate correction
`(x₁ ↦ B, x₀ ↦ B·[z,y], handle ↦ [y,s])` with `B = [s,z]` collapses, via the Jacobi
identity, to the square-collapsed cubic damage `B² · [B,s]`. -/
theorem cubicNeutral_damage_word (s z y : levelQuot G (3 + 1)) :
    commP s z ^ 2 * commP (commP s z) y * commP (commP s z) s *
        commP (commP z y) s * commP (commP y s) z =
      commP s z ^ 2 * commP (commP s z) s := by
  have h4 : commP (commP s z) y ∈ zLayer G 3 :=
    commP_mem_zLayer 3 le_rfl (cubicNeutral_commP_mem s z) y
  have hJ := cubicNeutral_jacobi s z y
  calc commP s z ^ 2 * commP (commP s z) y * commP (commP s z) s *
      commP (commP z y) s * commP (commP y s) z
      = commP s z ^ 2 * (commP (commP s z) y * commP (commP s z) s) *
        (commP (commP z y) s * commP (commP y s) z) := by group
    _ = commP s z ^ 2 * (commP (commP s z) s * commP (commP s z) y) *
        (commP (commP z y) s * commP (commP y s) z) := by
          rw [(zLayer_commute h4 (commP (commP s z) s)).eq]
    _ = commP s z ^ 2 * commP (commP s z) s *
        (commP (commP s z) y * commP (commP z y) s * commP (commP y s) z) := by group
    _ = commP s z ^ 2 * commP (commP s z) s := by rw [hJ, mul_one]

end Jacobi

/-! ## The neutral realization of the cubic damage -/

variable {K : IntermediateField ℚ_[2] ℚ̄₂} [FiniteDimensional ℚ_[2] K]
  [CompactSpace (GalK K)] [T2Space (GalK K)]
  [TotallyDisconnectedSpace (GalK K)]

omit [FiniteDimensional ℚ_[2] ↥K] [T2Space (GalK K)] in
/-- Commutator-valued one-coordinate corrections are neutral at **every** slot: the mod-16
digit of a commutator is trivial because `χ` lands in an abelian group. -/
private theorem stageCubic_commP_coordinate_mem {h : ℕ} {i : Fin (SqCore.sqRank h)}
    {a b : levelQuot (maxProPQuotient 2 (GalK K)) (3 + 1)}
    (hab : commP a b ∈ lambdaImage (maxProPQuotient 2 (GalK K)) (3 - 1) (3 + 1)) :
    rawDepthCoordinateCorrection i ⟨commP a b, hab⟩ ∈
      stageNeutralCorrections (K := K) (h := h) (k := 3) := by
  refine ⟨fun l ↦ ?_, fun l ↦ ?_⟩
  · rw [rawDepthCoordinateCorrection_apply]
    split
    · exact map_commP_eq_one (chiLevel (chiCycKTwo (K := K)) (3 + 1)) a b
    · exact map_one _
  · rw [rawDepthCoordinateCorrection_apply]
    split
    · exact map_commP_eq_one (chiLevel (chiCycKTwo (K := K)) (3 + 1)) a b
    · exact map_one _

/-- **The Jacobi realization of one cubic damage bracket.**  Abstract in the flip/partner
slot pair: given the handle row formula for the flip slot, the damage bracket against the
partner letter lies in the neutral shift span. -/
private theorem stageCubic_damage_mem {h : ℕ} (T : SqCyclotomicStageTuple K h 3)
    (hk : 3 ≤ 3) {iflip ipart : Fin (SqCore.sqRank h)}
    (happly : ∀ p : lambdaImage (maxProPQuotient 2 (GalK K)) (3 - 1) (3 + 1),
      ((rawDepthShiftHom
          (fun i ↦ canonLift (maxProPQuotient 2 (GalK K)) 3 (T.generators i)) hk)
        (rawDepthCoordinateCorrection iflip p)).1 =
        commP p.1 (canonLift (maxProPQuotient 2 (GalK K)) 3 (T.generators ipart))) :
    commP ((canonLift (maxProPQuotient 2 (GalK K)) 3 (T.generators 0)) ^ 2 ^ (3 - 2))
        (canonLift (maxProPQuotient 2 (GalK K)) 3 (T.generators ipart)) ∈
      stageNeutralShiftSpan T hk := by
  set s := canonLift (maxProPQuotient 2 (GalK K)) 3 (T.generators 0) with hs
  set y := canonLift (maxProPQuotient 2 (GalK K)) 3 (T.generators 2)
  set z := canonLift (maxProPQuotient 2 (GalK K)) 3 (T.generators ipart) with hz
  have hpB : commP s z ∈ lambdaImage (maxProPQuotient 2 (GalK K)) (3 - 1) (3 + 1) :=
    cubicNeutral_commP_mem s z
  have hpzy : commP z y ∈ lambdaImage (maxProPQuotient 2 (GalK K)) (3 - 1) (3 + 1) :=
    cubicNeutral_commP_mem z y
  have hpys : commP y s ∈ lambdaImage (maxProPQuotient 2 (GalK K)) (3 - 1) (3 + 1) :=
    cubicNeutral_commP_mem y s
  set F := rawDepthShiftHom
    (fun i ↦ canonLift (maxProPQuotient 2 (GalK K)) 3 (T.generators i)) hk
  set c2 : RawDepthCorrection (maxProPQuotient 2 (GalK K)) h 3 :=
    rawDepthCoordinateCorrection 2 ⟨commP s z, hpB⟩
  set c1a : RawDepthCorrection (maxProPQuotient 2 (GalK K)) h 3 :=
    rawDepthCoordinateCorrection 1 ⟨commP s z, hpB⟩
  set c1b : RawDepthCorrection (maxProPQuotient 2 (GalK K)) h 3 :=
    rawDepthCoordinateCorrection 1 ⟨commP z y, hpzy⟩
  set c3 : RawDepthCorrection (maxProPQuotient 2 (GalK K)) h 3 :=
    rawDepthCoordinateCorrection iflip ⟨commP y s, hpys⟩
  have hV : c2 * c1a * c1b * c3 ∈ stageNeutralCorrections (K := K) (h := h) (k := 3) :=
    Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _
      (stageCubic_commP_coordinate_mem hpB) (stageCubic_commP_coordinate_mem hpB))
      (stageCubic_commP_coordinate_mem hpzy)) (stageCubic_commP_coordinate_mem hpys)
  have hmem := stageNeutral_word_mem_shiftSpan (T := T) hk hV
  have e2 : (F c2).1 = commP s z ^ 2 * commP (commP s z) y :=
    rawDepthShiftHom_two_apply _ hk _
  have e1a : (F c1a).1 = commP (commP s z) s := rawDepthShiftHom_one_apply _ hk _
  have e1b : (F c1b).1 = commP (commP z y) s := rawDepthShiftHom_one_apply _ hk _
  have e3 : (F c3).1 = commP (commP y s) z := happly _
  have hword : sqCoreHandleDbarWord
      (fun i ↦ canonLift (maxProPQuotient 2 (GalK K)) 3 (T.generators i))
      (c2 * c1a * c1b * c3).correction = commP (s ^ 2 ^ (3 - 2)) z := by
    show (F (c2 * c1a * c1b * c3)).1 = commP (s ^ 2 ^ (3 - 2)) z
    rw [map_mul, map_mul, map_mul]
    show (F c2).1 * (F c1a).1 * (F c1b).1 * (F c3).1 = commP (s ^ 2 ^ (3 - 2)) z
    rw [e2, e1a, e1b, e3, cubicNeutral_damage_word s z y, hs, hz,
      stageDamage_decomposition T hk
        (canonLift (maxProPQuotient 2 (GalK K)) 3 (T.generators ipart)),
      show (2 : ℕ) ^ (3 - 3) = 1 from rfl, pow_one]
  rw [← hword]
  exact hmem

/-- **The cubic neutral damage supply, unconditionally.**  At the cubic stage every flip
damage bracket is realized by a four-coordinate correction whose entries are single
commutators — automatically mod-16 neutral — through the class-three Jacobi identity.
No hypothesis on `K` beyond finiteness, and no handle-count restriction. -/
theorem sqCubicNeutralDamageSupply_holds (h : ℕ) : SqCubicNeutralDamageSupply K h := by
  intro T j
  exact ⟨stageCubic_damage_mem T _ (rawDepthShiftHom_handleU_apply _ _ j),
    stageCubic_damage_mem T _ (rawDepthShiftHom_handleV_apply _ _ j)⟩

/-- The neutral damage supply at every stage `k ≥ 3`, via the tower collapse. -/
theorem sqStageNeutralDamageSupply_all {h : ℕ} (k : ℕ) (hk : 3 ≤ k)
    (T : SqCyclotomicStageTuple K h k) : SqStageNeutralDamageSupply T hk :=
  sqStageNeutralDamageSupply_of_cubic (sqCubicNeutralDamageSupply_holds h) k hk T

/-- **The kernel-adapted defect supply at exact odd degree**, now input-free: both halves
— the twisted-cocycle parity supply and the bracket-square residual — are theorems. -/
theorem sqKernelAdaptedDefectSupply_of_finrank {h : ℕ}
    (hdeg : Module.finrank ℚ_[2] K = 2 * h + 1) :
    SqKernelAdaptedDefectSupply K h :=
  sqKernelAdaptedDefectSupply_of_bracketSquare hdeg
    (fun k hk T ↦ sqStageBracketSquareNeutralSupply_of_cubic
      (sqCubicNeutralDamageSupply_holds h) k hk T)

/-- **The forward presentation theorem for odd-degree fields.**  The sole remaining per-`K`
input of the forward route — the mod-16 cubic neutral damage supply — is a theorem, so the
oriented presentation equivalence between the improved square presentation and `G_K(2)`
holds for every odd-degree `K` over the caller's marked bundle and nothing else.

`B` is a binder, never the axiom `markedRecipAt` (B5-K): marked reciprocity is used only
through cyclotomic surjectivity and sharp fibre lifting, both generic in the bundle. -/
theorem nonempty_orientedEquiv_oddDegree {Rec : LocalReciprocity} (B : MarkedRecip Rec K)
    (hodd : Odd (Module.finrank ℚ_[2] K)) :
    Nonempty (OrientedContinuousMulEquiv
      (SqCore.chiSq ((Module.finrank ℚ_[2] K - 1) / 2))
      (chiCycKTwo (K := K))) :=
  nonempty_orientedEquiv_oddDegree_of_cubicNeutralDamage B hodd
    (sqCubicNeutralDamageSupply_holds _)

#print axioms cubicNeutral_jacobi
#print axioms cubicNeutral_damage_word
#print axioms sqCubicNeutralDamageSupply_holds
#print axioms sqStageNeutralDamageSupply_all
#print axioms sqKernelAdaptedDefectSupply_of_finrank
#print axioms nonempty_orientedEquiv_oddDegree

end

end GQ2.Dyadic.LSquare
