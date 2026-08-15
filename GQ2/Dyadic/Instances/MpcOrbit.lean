/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Opus-5
-/
import GQ2.Dyadic.Instances.MpcPivot

/-!
# W83-ORBIT: the `M6` orbit question on `D_M 2 0`, made concrete

Wave 82 reduced the `ℚ₂(√−10)` row to one abstract move on `D_M 2 0`, `MpcPivShift 2`, MC1
§5.3's family `M6` at parameter one (`Y_c : C̄₀ ↦ B̄^{2c₁}·C̄₀`, `docs/dyadic/mc-design.md:211`),
and recorded the conflict around it: `CoreMixM.lean` §7 rules `⟨M4, M6, M7⟩` "structurally
obstructed ... (they are not symplectic, hence not reachable by any relator-preserving word
automorphism)", while `mc-design` §5.3 says the opposite ("they *are* in the stabilizer").

This module replaces the conflict by an **exact computation**: it evaluates the relator on the
`M6` substitution and reports the defect in closed form.

## What lands

1. **The defect of the `M6` substitution, exactly** (§1).  In *any* group, substituting
   `c ↦ u·c` into the `M_2` core word costs precisely three left conjugates of `u` inserted
   between the two halves, plus one on the right:

       mWord 2 a b (u*c) d = (a²[a,b]) · (u · u^{c⁻¹} · u^{c⁻²}) · (c⁴[c,d]) · u^{cd}

   (`mpcOrb_mWord_shift`).  Inside `D_M 2 0` the two halves are mutually inverse, so the whole
   defect collapses to a product of **four conjugates of `u`** (`mpcOrb_defect`):

       mWord 2 Ā B̄ (u·C̄₀) D̄ = (u · u^{C̄₀⁻¹} · u^{C̄₀⁻²})^{z} · u^{C̄₀D̄},   z := C̄₀⁴[C̄₀,D̄].

   At `u = B̄²` this is the entire content of `M6` at parameter one: `MpcPivShift 2` holds iff
   that element can be absorbed by a compensating change of the `Ā`, `B̄`, `D̄` letters.

2. **The recipe** (§2).  `mpcOrb_shift_of_marking`: a marking of `D_M 2 0` that kills the core
   word, generates topologically, carries the four χ-values of the marked generators, and moves
   the `C̄₀` row by `2B̄` produces `MpcPivShift 2` outright.  This is the only shape a
   construction of `M6` can have, and it reduces the row to a single word identity.

3. **The frame level cannot obstruct** (§3).  `mpcOrb_frame_shift`: the `M6`-shifted frame
   satisfies the *same* forced `Ā`-row relation `ν'(Ā) = −2^{α−1}ν'(C̄₀)` that every marking of
   `D_M 2 0` satisfies, and `mpcOrb_chi_shift`: it preserves χ on the moved row.  So the
   obstruction claimed by `CoreMixM` §7 is not visible at the abelianized frame, where its
   "not symplectic" reason lives: the `ℤ₂`-symplectic defect `ω(Ā′,C̄₀′) = 2c₁` of the hand
   check is not an invariant of this relator, because the relator's `Ā²` factor makes the
   whole of `2Λ²` available as slack (§4 of the lane note).

## What does not land

**The decision.**  `MpcPivShift 2` is neither proved nor refuted here, and the lane note says
exactly why in both directions.  What changed is that the ruling which made it look decided is
now known to be unsound *as an argument*, and the residue is one explicit word identity in a
4-generator pro-2 group rather than a claim about a stabilizer.

Declaration prefix `mpcOrb` (namespace `GQ2.Dyadic.Instances.MpcOrb`).  No `sorry`, no new
axiom, no `native_decide`, no `maxHeartbeats`, no `maxRecDepth`.
-/

namespace GQ2.Dyadic.Instances.MpcOrb

open GQ2 GQ2.Dyadic GQ2.Dyadic.MarkedCore Multiplicative
open GQ2.Dyadic.Instances.MpcPiv

noncomputable section

/-! ## §1 The defect of the `M6` substitution

`M6` is the substitution `C̄₀ ↦ u·C̄₀` with `u = B̄^{2c₁}`.  The following identity is a free
group computation: it holds in every group, with no relation used, and it isolates exactly what
the substitution costs. -/

section Defect

variable {G : Type*} [Group G]

/-- **The `M6` substitution, evaluated.**  Substituting `c ↦ u·c` into the `M_2` core word
inserts `u · u^{c⁻¹} · u^{c⁻²}` between the two halves and appends `u^{cd}`.  A free-group
identity: no relation is used, and `u` is arbitrary.

The three inserted factors are the `u`'s of `(u·c)³ = u·u^{c⁻¹}·u^{c⁻²}·c³`; the appended one is
the `u` of `(u·c)^d`. -/
theorem mpcOrb_mWord_shift (a b c d u : G) :
    mWord 2 a b (u * c) d
      = a ^ 2 * commP a b * (u * conjP u c⁻¹ * conjP u (c⁻¹ * c⁻¹))
          * (c ^ 4 * commP c d) * conjP u (c * d) := by
  have e4 : ∀ x : G, x ^ 4 = x * x * x * x := fun x => by
    simp only [show (4 : ℕ) = 1 + 1 + 1 + 1 from rfl, pow_add, pow_one]
  simp only [mWord, commP, conjP, show (2 : ℕ) ^ 2 = 4 from rfl, e4]
  group

end Defect

section DefectDM

/-- The `M_2` core relation at the marked generators of `D_M 2 0` (the handle block is empty). -/
theorem mpcOrb_relation :
    mWord 2 (dmA 2 0) (dmB 2 0) (dmC 2 0) (dmD 2 0) = 1 := by
  have h := dm_relation 2 0
  rw [mRelWord, handleWord_zero, mul_one] at h
  exact h

/-- The two halves of the relator are mutually inverse in `D_M 2 0`. -/
theorem mpcOrb_head_eq_inv_tail :
    dmA 2 0 ^ 2 * commP (dmA 2 0) (dmB 2 0)
      = (dmC 2 0 ^ 4 * commP (dmC 2 0) (dmD 2 0))⁻¹ := by
  refine eq_inv_of_mul_eq_one_left ?_
  have h := mpcOrb_relation
  rw [mWord, show (2 : ℕ) ^ 2 = 4 from rfl] at h
  rw [← h]
  group

/-- **THE DEFECT OF `M6`, IN CLOSED FORM.**  Inside `D_M 2 0` the head of the relator is the
inverse of its tail, so the whole cost of `C̄₀ ↦ u·C̄₀` is a product of **four conjugates of
`u`**: three of them conjugated by the tail `z = C̄₀⁴[C̄₀,D̄]`, one by `C̄₀D̄`.

At `u = B̄^{2c₁}` this is `M6` at parameter `c₁`, and `MpcPivShift 2` (the `√−10` row's whole
residue, wave 82 §6) holds exactly when this element can be cancelled by a compensating change
of `Ā`, `B̄` and `D̄` : the shape §2 packages. -/
theorem mpcOrb_defect (u : (DM 2 0 : Type)) :
    mWord 2 (dmA 2 0) (dmB 2 0) (u * dmC 2 0) (dmD 2 0)
      = conjP (u * conjP u (dmC 2 0)⁻¹ * conjP u ((dmC 2 0)⁻¹ * (dmC 2 0)⁻¹))
            (dmC 2 0 ^ 4 * commP (dmC 2 0) (dmD 2 0))
          * conjP u (dmC 2 0 * dmD 2 0) := by
  rw [mpcOrb_mWord_shift, mpcOrb_head_eq_inv_tail]
  simp only [conjP, mul_assoc]

end DefectDM

/-! ## §2 The recipe

Any construction of `M6` has to produce a marking of `D_M 2 0` killing the core word, with the
right χ-values and the right `C̄₀` row.  This section packages that into a single theorem, so
that the `√−10` row costs exactly one word identity plus the two routine side conditions. -/

section Recipe

/-- **THE RECIPE FOR `MpcPivShift`.**  A four-letter marking of `D_M 2 0` that

* kills the `M_2` core word (`hrel`),
* generates `D_M 2 0` topologically (`hgen`),
* carries the χ-values of the marked generators (`hchi*`), and
* moves the `C̄₀` row by twice the `B̄` row on every marking (`hrow`),

is `M6` at parameter one: it yields `MpcPivShift 2`, hence (wave 82's
`mpcPiv_genAsmBranch_sqrtNegTen_of_shift`) the `√−10` branch datum at the row's own canonical
marking with no clause.

Surjectivity comes from the closed range of a continuous map out of a compact group, and
injectivity from `profinite_hopfian`; χ-preservation is hom-extensionality against the four
values, so the *only* real content a caller must supply is `hrel`. -/
theorem mpcOrb_shift_of_marking {a b c d : (DM 2 0 : Type)}
    (hrel : mWord 2 a b c d = 1)
    (hgen : (Subgroup.closure ({a, b, c, d} : Set (DM 2 0 : Type))).topologicalClosure = ⊤)
    (hchiA : chiM 2 0 a = 1) (hchiB : chiM 2 0 b = -1) (hchiC : chiM 2 0 c = 1)
    (hchiD : chiM 2 0 d = mUnit 2)
    (hrow : ∀ f : ContinuousMonoidHom (DM 2 0 : Type) (Multiplicative ℤ_[2]),
      toAdd (f c) = toAdd (f (dmC 2 0)) + 2 * toAdd (f (dmB 2 0))) :
    MpcPivShift 2 := by
  classical
  have hrelm : mRelWord 2 (coreMark (h := 0) a b c d) = 1 := by
    rw [mRelWord_coreMark]; exact hrel
  set Phi := mLiftHom 2 0 (isProP_DM 2 0) (coreMark (h := 0) a b c d) hrelm with hPhi
  have hA : Phi (dmA 2 0) = a := by
    rw [hPhi, dmA, mLiftHom_gen, coreMark_zero]
  have hB : Phi (dmB 2 0) = b := by
    rw [hPhi, dmB, mLiftHom_gen, coreMark_one]
  have hC : Phi (dmC 2 0) = c := by
    rw [hPhi, dmC, mLiftHom_gen, coreMark_two]
  have hD : Phi (dmD 2 0) = d := by
    rw [hPhi, dmD, mLiftHom_gen, coreMark_three]
  -- surjectivity: the range is a closed subgroup containing the four letters
  have hsurj : Function.Surjective Phi := by
    have hclosed : IsClosed ((Phi.toMonoidHom.range : Subgroup (DM 2 0 : Type)) :
        Set (DM 2 0 : Type)) := by
      rw [MonoidHom.coe_range Phi.toMonoidHom]
      exact (isCompact_range Phi.continuous_toFun).isClosed
    have hsub : Subgroup.closure ({a, b, c, d} : Set (DM 2 0 : Type))
        ≤ Phi.toMonoidHom.range := by
      rw [Subgroup.closure_le]
      rintro x (rfl | rfl | rfl | rfl)
      exacts [⟨dmA 2 0, hA⟩, ⟨dmB 2 0, hB⟩, ⟨dmC 2 0, hC⟩, ⟨dmD 2 0, hD⟩]
    have hle := Subgroup.topologicalClosure_minimal _ hsub hclosed
    rw [hgen, top_le_iff] at hle
    intro y
    have : y ∈ Phi.toMonoidHom.range := by rw [hle]; trivial
    exact this
  have hbij : Function.Bijective Phi :=
    ⟨profinite_hopfian (dm_topologicallyFinGen_zero 2) Phi hsurj, hsurj⟩
  refine ⟨continuousMulEquivOfBijective Phi hbij, ?_, ?_⟩
  · -- χ-preservation, by hom-extensionality against the four values
    have hcomp : (chiM 2 0).comp Phi = chiM 2 0 := by
      refine dm_hom_ext _ _ (fun i => ?_)
      fin_cases i
      · show chiM 2 0 (Phi (dmA 2 0)) = chiM 2 0 (dmA 2 0)
        rw [hA, hchiA, chiM_dmA]
      · show chiM 2 0 (Phi (dmB 2 0)) = chiM 2 0 (dmB 2 0)
        rw [hB, hchiB, chiM_dmB]
      · show chiM 2 0 (Phi (dmC 2 0)) = chiM 2 0 (dmC 2 0)
        rw [hC, hchiC, chiM_dmC]
      · show chiM 2 0 (Phi (dmD 2 0)) = chiM 2 0 (dmD 2 0)
        rw [hD, hchiD, chiM_dmD]
    intro x
    exact congrArg (fun F : ContinuousMonoidHom (DM 2 0 : Type) ℤ_[2]ˣ => F x) hcomp
  · intro f
    show toAdd (f (Phi (dmC 2 0))) = _
    rw [hC]
    exact hrow f

end Recipe

/-! ## §3 The frame level cannot obstruct

`CoreMixM` §7's reason for ruling `M6` out is that it "is not symplectic".  The frame of
`D_M 2 0` carries exactly one relation, the forced `Ā`-row `ν'(Ā) = −2^{α−1}·ν'(C̄₀)`
(`nu_dmA_eq`), and the `M6` shift respects it: the two statements below say that the shifted
frame is a frame and that the shifted `C̄₀` row keeps its χ-value.  So whatever the truth about
`M6`, it is not settled at this level. -/

section Frame

/-- **The `M6`-shifted frame is a frame.**  If the `C̄₀` row moves by `2c₁·ν'(B̄)` then the
forced `Ā` row moves by `−4c₁·ν'(B̄)`, and the relation `ν'(Ā) = −2·ν'(C̄₀)` of `D_M 2 0` still
holds.  (The relation vector `ρ_M = 2Ā + 2^α C̄₀` is the only constraint the frame carries.) -/
theorem mpcOrb_frame_shift (c₁ : ℤ_[2])
    (nu' : ContinuousMonoidHom (DM 2 0 : Type) (Multiplicative ℤ_[2])) :
    toAdd (nu' (dmA 2 0)) - 4 * c₁ * toAdd (nu' (dmB 2 0))
      = -(2 : ℤ_[2]) ^ (2 - 1)
        * (toAdd (nu' (dmC 2 0)) + 2 * c₁ * toAdd (nu' (dmB 2 0))) := by
  rw [nu_dmA_eq 2 0 (by omega) nu']
  ring

/-- **The `M6` shift is χ-neutral on the moved row.**  `χ_M(B̄^{2c₁}·C̄₀) = χ_M(C̄₀)`, because
`χ_M(B̄) = −1` and the exponent is even.  This is why the family's parameter is `2c₁` and not
`c₁`: the odd shifts are the ones χ forbids (and `mpcPiv_shift_necessary` shows the even one at
an odd parameter is exactly what the `√−10` row needs). -/
theorem mpcOrb_chi_shift (c₁ : ℕ) :
    chiM 2 0 (dmB 2 0 ^ (2 * c₁) * dmC 2 0) = chiM 2 0 (dmC 2 0) := by
  rw [map_mul, map_pow, chiM_dmB, chiM_dmC, pow_mul]
  norm_num

end Frame

/-! ## §4 Axiom pins

One line per declaration, measured against the mirror.  Every declaration of this module is on
the **standard three** (`propext`, `Classical.choice`, `Quot.sound`): the defect identity is a
free-group computation, the recipe is `mLiftHom` plus `profinite_hopfian`, and the frame
statements are `nu_dmA_eq` and `chiM`.  **This lane introduces no axiom**, and in particular the
recipe is free of `peripheralCyclotomicAction`: a construction of `M6` fed through
`mpcOrb_shift_of_marking` would carry only wave 81's set on the `√−10` row, through
`mpcPiv_genAsmBranch_sqrtNegTen_of_shift`.

No `sorry`, no new axiom, no `native_decide`, no `maxHeartbeats`, no `maxRecDepth`. -/

section AxiomPins

#print axioms mpcOrb_mWord_shift
#print axioms mpcOrb_relation
#print axioms mpcOrb_head_eq_inv_tail
#print axioms mpcOrb_defect
#print axioms mpcOrb_shift_of_marking
#print axioms mpcOrb_frame_shift
#print axioms mpcOrb_chi_shift

end AxiomPins

end

end GQ2.Dyadic.Instances.MpcOrb
