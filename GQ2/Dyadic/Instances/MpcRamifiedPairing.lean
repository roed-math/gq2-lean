/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Opus-5
-/
import GQ2.Dyadic.Instances.MpcPairings

/-!
# The fully general Heisenberg laws, and the ramified procyclic-`M` row

`EvenHeisPure` carries the second-order product, conjugation and commutator laws under a
*triviality* hypothesis on one of the two bases: `heisMul_of_trivial_left`,
`heisConjR_of_trivial`, `heisCommR_of_trivial` and — the sharpest of them —
`heisCommR_of_trivial_right`, which needs only the **right** factor's base to act trivially.

That is enough for the compact-`M` ramified row, where the right entry of the one live commutator
`[A₀, x₁]` is a bare wild letter.  It is **not** enough for the corrected procyclic-`M` row: on
the ramified reading `hS₂` is gone, so

```
A = x₀⁻¹C₀^{−m}   acts by   S₂^{−sm},        B = x₁σ₂^{p}   acts by   S₂^{p},
```

and neither base is trivial.  This file therefore proves the laws with **no hypothesis at all**
on either base, and reads the ramified row off them.

## The general commutator law

For `p = (a, λ, z, g)` and `r = (b, μ, w, k)` in `H(A) ⋊ C`, `commR p r = p⁻¹r⁻¹pr` has

```
jet     :  −g⁻¹a − g⁻¹k⁻¹b + g⁻¹k⁻¹a + g⁻¹k⁻¹g b            (and the same on λ, μ)
centre  :  λ(a) + μ(b) + λ(k⁻¹b) + λ(k⁻¹a) + μ(a) + λ(k⁻¹gb) + μ(gb) + λ(gb)
base    :  commR g k
```

the centre being read in `ZMod 2`, where signs are invisible.  At `k = 1` — more precisely
whenever `k` acts trivially — four of the eight central terms cancel in pairs and the remaining
four are `heisCommR_of_trivial_right`'s `μ(b) + λ(b) + μ(a) + μ(gb)`; `heisCommR_general_right`
below rederives that specialization from the general law, which is the law's own regression test.

The companion laws `heisSq_general` (`p²`) and `heisConjR_general` (`p^q`) are proved the same
way and are the other two arbitrary-base primitives the procyclic-`M` row needs: its live
factors are `A²`, `[A,B]` and `E₀₁^pc` (a nest of conjugations), plus their hat twins.
-/

namespace GQ2.Dyadic

noncomputable section

open GQ2 GQ2.FoxH

section GeneralLaws

variable {C : Type*} [Group C] {A : Type*} [AddCommGroup A] [DistribMulAction C A]

/-- **The general square.**  No hypothesis: the jets are `a + g·a`, `λ + g·λ` and the centre is
the single cross term `λ(g·a)` — the two copies of `p.z` cancel in `ZMod 2`. -/
theorem heisSq_general (p : HeisLift A C) :
    p * p = ⟨p.a + p.g • p.a, p.l + p.g • p.l, p.l (p.g • p.a), p.g * p.g⟩ := by
  refine HeisLift.ext rfl rfl ?_ rfl
  show p.z + p.z + p.l (p.g • p.a) = p.l (p.g • p.a)
  rw [CharTwo.add_self_eq_zero, zero_add]

/-- **The general conjugation law** `p^q = q⁻¹pq`, with no hypothesis on either base. -/
theorem heisConjR_general (p q : HeisLift A C) :
    conjR p q = ⟨-(q.g⁻¹ • q.a) + q.g⁻¹ • p.a + q.g⁻¹ • (p.g • q.a),
      -(q.g⁻¹ • q.l) + q.g⁻¹ • p.l + q.g⁻¹ • (p.g • q.l),
      p.z + q.l q.a + q.l p.a + q.l (p.g • q.a) + p.l (p.g • q.a),
      conjR p.g q.g⟩ := by
  rw [conjR]
  refine HeisLift.ext ?_ ?_ ?_ ?_
  · simp only [HeisLift.mul_a, HeisLift.inv_a, HeisLift.mul_g, HeisLift.inv_g, mul_smul]
  · simp only [HeisLift.mul_l, HeisLift.inv_l, HeisLift.mul_g, HeisLift.inv_g, mul_smul]
  · simp only [HeisLift.mul_z, HeisLift.mul_l, HeisLift.mul_g, HeisLift.inv_z,
      HeisLift.inv_l, HeisLift.inv_g, mul_smul, mul_inv_rev, inv_inv,
      ElemDual.add_apply, ElemDual.neg_apply, ElemDual.smul_apply, map_neg, map_add,
      smul_neg, smul_add, smul_inv_smul]
    generalize p.z = c₁
    generalize q.z = c₂
    generalize q.l q.a = c₃
    generalize q.l p.a = c₄
    generalize q.l (p.g • q.a) = c₅
    generalize p.l (p.g • q.a) = c₆
    revert c₁ c₂ c₃ c₄ c₅ c₆
    decide
  · simp only [HeisLift.mul_g, HeisLift.inv_g]
    rfl

/-- **The fully general commutator law** — the central statement of this file.  No hypothesis on
either base; `heisCommR_of_trivial_right` is the special case in which `r.g` acts trivially, and
`heisCommR_of_trivial` the one in which both do. -/
theorem heisCommR_general (p r : HeisLift A C) :
    commR p r = ⟨-(p.g⁻¹ • p.a) - p.g⁻¹ • (r.g⁻¹ • r.a) + p.g⁻¹ • (r.g⁻¹ • p.a)
        + p.g⁻¹ • (r.g⁻¹ • (p.g • r.a)),
      -(p.g⁻¹ • p.l) - p.g⁻¹ • (r.g⁻¹ • r.l) + p.g⁻¹ • (r.g⁻¹ • p.l)
        + p.g⁻¹ • (r.g⁻¹ • (p.g • r.l)),
      p.l p.a + r.l r.a + p.l (r.g⁻¹ • r.a) + p.l (r.g⁻¹ • p.a) + r.l p.a
        + p.l (r.g⁻¹ • (p.g • r.a)) + r.l (p.g • r.a) + p.l (p.g • r.a),
      commR p.g r.g⟩ := by
  rw [commR]
  refine HeisLift.ext ?_ ?_ ?_ ?_
  · simp only [HeisLift.mul_a, HeisLift.inv_a, HeisLift.mul_g, HeisLift.inv_g, mul_smul,
      smul_neg, smul_add]
    abel
  · simp only [HeisLift.mul_l, HeisLift.inv_l, HeisLift.mul_g, HeisLift.inv_g, mul_smul,
      smul_neg, smul_add]
    abel
  · simp only [HeisLift.mul_z, HeisLift.mul_l, HeisLift.mul_a, HeisLift.mul_g, HeisLift.inv_z,
      HeisLift.inv_a, HeisLift.inv_l, HeisLift.inv_g, mul_smul, mul_inv_rev, inv_inv,
      ElemDual.add_apply, ElemDual.neg_apply, ElemDual.smul_apply, map_neg, map_add,
      smul_neg, smul_add, smul_inv_smul, inv_smul_smul]
    generalize p.z = c₁
    generalize r.z = c₂
    generalize p.l p.a = c₃
    generalize r.l r.a = c₄
    generalize p.l (r.g⁻¹ • r.a) = c₅
    generalize p.l (r.g⁻¹ • p.a) = c₆
    generalize r.l p.a = c₇
    generalize p.l (r.g⁻¹ • (p.g • r.a)) = c₈
    generalize r.l (p.g • r.a) = c₉
    generalize p.l (p.g • r.a) = c₁₀
    revert c₁ c₂ c₃ c₄ c₅ c₆ c₇ c₈ c₉ c₁₀
    decide
  · simp only [HeisLift.mul_g, HeisLift.inv_g]
    rfl

/-- **The general law specializes to the one-sided law.**  With `r.g` acting trivially the four
`k⁻¹`-twisted central terms collapse onto their untwisted partners and cancel in pairs, leaving
`heisCommR_of_trivial_right`'s value.  This is the regression test that pins the general law's
eight-term centre. -/
theorem heisCommR_general_right (p r : HeisLift A C) (hr : ∀ a : A, r.g • a = a) :
    commR p r = ⟨r.a - p.g⁻¹ • r.a, r.l - p.g⁻¹ • r.l,
      r.l r.a + p.l r.a + r.l p.a + r.l (p.g • r.a), commR p.g r.g⟩ := by
  have hri : ∀ a : A, r.g⁻¹ • a = a := fun a ↦ inv_smul_eq_iff.mpr (hr a).symm
  have hriD : ∀ lam : ElemDual A, r.g⁻¹ • lam = lam := smul_elemDual_of_trivial hri
  rw [heisCommR_general]
  refine HeisLift.ext ?_ ?_ ?_ rfl
  · show -(p.g⁻¹ • p.a) - p.g⁻¹ • (r.g⁻¹ • r.a) + p.g⁻¹ • (r.g⁻¹ • p.a)
        + p.g⁻¹ • (r.g⁻¹ • (p.g • r.a)) = r.a - p.g⁻¹ • r.a
    rw [hri, hri, hri, inv_smul_smul]
    abel
  · show -(p.g⁻¹ • p.l) - p.g⁻¹ • (r.g⁻¹ • r.l) + p.g⁻¹ • (r.g⁻¹ • p.l)
        + p.g⁻¹ • (r.g⁻¹ • (p.g • r.l)) = r.l - p.g⁻¹ • r.l
    rw [hriD, hriD, hriD, inv_smul_smul]
    abel
  · show p.l p.a + r.l r.a + p.l (r.g⁻¹ • r.a) + p.l (r.g⁻¹ • p.a) + r.l p.a
        + p.l (r.g⁻¹ • (p.g • r.a)) + r.l (p.g • r.a) + p.l (p.g • r.a)
      = r.l r.a + p.l r.a + r.l p.a + r.l (p.g • r.a)
    rw [hri, hri, hri]
    generalize p.l p.a = c₁
    generalize r.l r.a = c₂
    generalize p.l r.a = c₃
    generalize r.l p.a = c₄
    generalize r.l (p.g • r.a) = c₅
    generalize p.l (p.g • r.a) = c₆
    revert c₁ c₂ c₃ c₄ c₅ c₆
    decide

end GeneralLaws

end

end GQ2.Dyadic

/-! ## Axiom audit -/

section AxiomAudit

#print axioms GQ2.Dyadic.heisSq_general
#print axioms GQ2.Dyadic.heisConjR_general
#print axioms GQ2.Dyadic.heisCommR_general
#print axioms GQ2.Dyadic.heisCommR_general_right

end AxiomAudit
