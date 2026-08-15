/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Opus-5
-/
import GQ2.Dyadic.Instances.MpcNormValues

/-!
# W82-PIVOT: the `ε = true` pivot at `ℚ₂(√−10)`, and what it really costs

Wave 81 left the `√−10` row carrying exactly one hypothesis, the pivot conjunct

    ∃ γ : ℤ₂ˣ, ν'(C̄₀) = γ · 2,

and proved that wave 80 §3.3's trapping argument cannot supply it: that argument needs `ν'(B̄)`
even, and this row's own `λ(−1) = 1` makes it odd.  This module settles what the two live routes
give.

## What lands

1. **The `ker χ_M` image, exactly** (§2).  Wave 80 §3.3 displayed

       ν'(ker χ_M) = ⟨ν'(C̄₀), 2·ν'(B̄)⟩

   and said "the displayed identity is not a theorem of this tree".  With wave 81's freeness of
   `ℤ₂ˣ` it is one now, in both directions and at every marking of `D_M 2 0`
   (`mpcPiv_kerChi_le`, `mpcPiv_kerChi_ge`).

2. **The trapping route is exhausted, structurally** (§3).  At `ν'(B̄)` odd the right-hand side
   above is `2ℤ₂` *whatever* `ν'(C̄₀)` is, so the lower half of the level is satisfied by
   `B̄^{2y}` alone and can never contradict anything: `mpcPiv_kerChi_full_of_odd_dmB`.  This is
   wave 80's hand counterexample promoted from one marking to the whole technique, and it also
   re-proves the `ε = false` pivot in one line (`mpcPiv_pivot_of_even_dmB`) from the same
   identity.

3. **The pivot is exactly an orbit question** (§4).  Any two oriented equivalences differ by a
   χ-preserving automorphism (`mpcPiv_transport`), so the pivot at *some* oriented equivalence
   is equivalent to a statement about `D_M 2 0` and the chosen marking alone
   (`mpcPiv_pivot_iff_orbit`): both implications, no arithmetic.

4. **The named residual, and the branch datum over it** (§5).  `MpcPivShift`, MC1 §5.3's family
   `M6` (`Y_c : C̄₀ ↦ B̄^{2c₁}·C̄₀`, `docs/dyadic/mc-design.md:211`) at parameter one, is enough:
   `mpcPiv_genAsmBranch_sqrtNegTen_of_shift` produces the `√−10` branch datum **at the row's own
   canonical marking** over it and nothing else.  It is also *necessary*: every χ-preserving
   automorphism moves the pivot row inside `ν'(C̄₀)ℤ₂ + 2ν'(B̄)ℤ₂` (`mpcPiv_orbit_shape`), and in
   the failing case only an odd `B̄`-coefficient can rescue it (`mpcPiv_shift_necessary`).

5. **The branch datum, unconditionally, but untied** (§6).  `GenAsmBranch` does not pin `nuP` to
   the row's canonical marking: the field is "a construction, not an obligation"
   (`GeneralAssembly.lean:212`) and `MarkedCoreRealization` has no orientation clause.  So the
   acceptance statement `mpcPiv_genAsmBranch_sqrtNegTen` is provable with no clause at all, by
   carrying the transported marking itself.  **Read §6's warning**: this is not the pivot, and a
   branch datum built this way cannot serve `GenAsmRowResidual.cand`, whose committed producer
   `MProcyclicCore.mpcWordCertificate` lives at `mpcNu 2 1 1`.

## What does not land

The pivot itself, at the row's canonical marking.  §3 shows why no image-level argument can give
it, and §4 reduces it to `MpcPivShift`, which is MC1 §5.3's S3 residue: `CoreMixM.lean` §7 rules
`⟨M4, M6, M7⟩` "structurally obstructed rather than merely unbuilt (they are not symplectic,
hence not reachable by any relator-preserving word automorphism)".  If that ruling is right then
`MpcPivShift` is **false**, `v₂(ν'(C̄₀))` is an invariant of the field rather than of the marking,
and the pivot has to be computed, not normalized.  §4 is what makes that fork sharp: the pivot
holds at some oriented equivalence *if and only if* the orbit reaches valuation one.

⚠⚠ **[W84-HOUSE, as of `45f9c42d`: the quoted ruling is now known to be UNSOUND AS AN ARGUMENT,
so the conditional above must not be read as evidence either way.**  W83-ORBIT
(`Instances/MpcOrbit.lean`, `docs/dyadic/w83-orbit-note.md` §4) showed that the premise the
ruling rests on does not exist on this core: there is no `ℤ₂`-symplectic invariant of `D_M` to
violate, because the relator `P_M = Ā²[Ā,B̄]C̄₀^{2^α}[C̄₀,D̄]` carries the square `Ā²` and is
therefore not a product of commutators.  Demushkin duality pairs into `H²(G, ℤ/q)` with `q = 2`
here, i.e. only mod 2, and mod 2 `M6` is the **identity**, hence an isometry of the only bilinear
invariant there is.  Two Lean statements pin the same conclusion one level down:
`mpcOrb_frame_shift` shows the `M6`-shifted frame satisfies the *same* forced `Ā`-row relation
`ν'(Ā) = −2^{α−1}ν'(C̄₀)` that every marking of `D_M 2 0` satisfies, and `mpcOrb_chi_shift` shows
the shift is χ-neutral on the moved row.  So the frame level, where the quoted reason lives,
cannot obstruct `M6` at all.

What replaces the fork: `mpcOrb_shift_iff_marking` makes `MpcPivShift 2` **equivalent** to an
explicit word problem in `D_M 2 0` (a four-letter marking killing the `M_2` core word, generating
topologically, carrying the four χ-values, and moving the `C̄₀` row by `2B̄`), and `mpcOrb_defect`
computes the cost of the substitution in closed form as a product of four conjugates of `u`.
`MpcPivShift 2` is **open**: neither built nor refuted.  `CoreMixM` §7's *conclusion* may still be
true; its *reason* is not a proof, and the campaign should stop treating `M6` as settled in the
negative.  The producer that now exists for `MpcPivShift`, `mpcOrb_shift_of_marking`, lives in
`Instances/MpcOrbit.lean`, which no scoreboard row imports; see the W84-HOUSE note.]**

Declaration prefix `mpcPiv` (namespace `GQ2.Dyadic.Instances.MpcPiv`).  No `sorry`, no new
axiom, no `native_decide`, no `maxHeartbeats`, no `maxRecDepth`.
-/

namespace GQ2.Dyadic.Instances.MpcPiv

open GQ2 GQ2.Dyadic GQ2.Dyadic.MarkedCore Multiplicative
open GQ2.Dyadic.Instances.MpcCert GQ2.Dyadic.Instances.MpcRow GQ2.Dyadic.Instances.MpcNorm
open GQ2.Dyadic.FieldUnimod GQ2.Dyadic.FieldBranchId
open GQ2.Dyadic.Fields

local notation "ℚ̄₂" => AlgebraicClosure ℚ_[2]

noncomputable section

/-! ## §1 The comparison subgroup at a general pivot value

Wave 81's `mpcNorm_compSub b₁ b₂` is the `ℤ₂`-span of `(−1, b₁)`, `(mUnit 2, b₂)` and `(1, 4)`.
Replacing the hardcoded `4` by the marking's own `ν'(C̄₀)` is what turns the trap from a
sufficient condition into an **exact** description of the image of `(χ_M, ν')`: the four marked
generators land in it with no hypothesis at all, because `ν'(Ā) = −2·ν'(C̄₀)` is the frame's own
relation. -/

section Span

/-- The `ℤ₂`-span of `(−1, v₁)`, `(mUnit 2, v₂)` and `(1, v₃)` inside `ℤ₂ˣ × ℤ₂`. -/
def mpcPiv_span (v₁ v₂ v₃ : ℤ_[2]) : Subgroup (ℤ_[2]ˣ × Multiplicative ℤ_[2]) where
  carrier := Set.range fun p : ℤ_[2] × ℤ_[2] × ℤ_[2] =>
    (GQ2.zpowZtwo GQ2.isProP_two_unitsPadicInt (-1 : ℤ_[2]ˣ) p.1
        * GQ2.zpowZtwo GQ2.isProP_two_unitsPadicInt (mUnit 2) p.2.1,
      ofAdd (p.1 * v₁ + p.2.1 * v₂ + p.2.2 * v₃))
  mul_mem' := by
    rintro _ _ ⟨⟨s, t, u⟩, rfl⟩ ⟨⟨s', t', u'⟩, rfl⟩
    refine ⟨(s + s', t + t', u + u'), Prod.ext ?_ ?_⟩ <;>
      dsimp only [Prod.fst_mul, Prod.snd_mul]
    · rw [GQ2.zpowZtwo_add, GQ2.zpowZtwo_add]
      exact mul_mul_mul_comm _ _ _ _
    · rw [← ofAdd_add]
      congr 1
      ring
  one_mem' := by
    refine ⟨(0, 0, 0), Prod.ext ?_ ?_⟩ <;> dsimp only [Prod.fst_one, Prod.snd_one]
    · rw [mpcNorm_zpowZtwo_zero, mpcNorm_zpowZtwo_zero, one_mul]
    · rw [show ((0 : ℤ_[2]) * v₁ + (0 : ℤ_[2]) * v₂ + (0 : ℤ_[2]) * v₃) = 0 by ring]
      rfl
  inv_mem' := by
    rintro _ ⟨⟨s, t, u⟩, rfl⟩
    refine ⟨(-s, -t, -u), Prod.ext ?_ ?_⟩ <;> dsimp only [Prod.fst_inv, Prod.snd_inv]
    · rw [mpcNorm_zpowZtwo_neg, mpcNorm_zpowZtwo_neg, ← mul_inv]
    · rw [← ofAdd_neg]
      congr 1
      ring

theorem mpcPiv_isClosed_span (v₁ v₂ v₃ : ℤ_[2]) :
    IsClosed (mpcPiv_span v₁ v₂ v₃ : Set (ℤ_[2]ˣ × Multiplicative ℤ_[2])) := by
  have hcont : Continuous fun p : ℤ_[2] × ℤ_[2] × ℤ_[2] =>
      ((GQ2.zpowZtwo GQ2.isProP_two_unitsPadicInt (-1 : ℤ_[2]ˣ) p.1
          * GQ2.zpowZtwo GQ2.isProP_two_unitsPadicInt (mUnit 2) p.2.1 : ℤ_[2]ˣ),
        (ofAdd (p.1 * v₁ + p.2.1 * v₂ + p.2.2 * v₃) : Multiplicative ℤ_[2])) := by
    refine Continuous.prodMk (Continuous.mul ?_ ?_) ?_
    · exact (GQ2.continuous_zpowZtwo _ _).comp continuous_fst
    · exact (GQ2.continuous_zpowZtwo _ _).comp (continuous_fst.comp continuous_snd)
    · exact continuous_ofAdd.comp
        ((((continuous_fst.mul continuous_const).add
          ((continuous_fst.comp continuous_snd).mul continuous_const)).add
          ((continuous_snd.comp continuous_snd).mul continuous_const)))
  exact (isCompact_range hcont).isClosed

/-- **All four marked generators land in the span**, with no hypothesis on the marking: `B̄`,
`C̄₀` and `D̄` by construction and `Ā` by `nu_dmA_eq` at `α = 2`. -/
theorem mpcPiv_gens_mem (nu' : ContinuousMonoidHom (DM 2 0 : Type) (Multiplicative ℤ_[2]))
    (i : Fin (coreRank 0)) :
    mpcNorm_compPhi nu' (dmGen 2 0 i)
      ∈ mpcPiv_span (toAdd (nu' (dmB 2 0))) (toAdd (nu' (dmD 2 0))) (toAdd (nu' (dmC 2 0))) := by
  rcases mCoreIdx_cases i with rfl | rfl | rfl | rfl
  · refine ⟨(0, 0, -2), Prod.ext ?_ ?_⟩
    · show GQ2.zpowZtwo GQ2.isProP_two_unitsPadicInt (-1 : ℤ_[2]ˣ) 0
          * GQ2.zpowZtwo GQ2.isProP_two_unitsPadicInt (mUnit 2) 0 = chiM 2 0 (dmA 2 0)
      rw [mpcNorm_zpowZtwo_zero, mpcNorm_zpowZtwo_zero, one_mul, chiM_dmA]
    · have hval : (0 : ℤ_[2]) * toAdd (nu' (dmB 2 0)) + (0 : ℤ_[2]) * toAdd (nu' (dmD 2 0))
          + (-2 : ℤ_[2]) * toAdd (nu' (dmC 2 0)) = toAdd (nu' (dmA 2 0)) := by
        rw [nu_dmA_eq 2 0 one_le_two nu']
        norm_num
      show ofAdd ((0 : ℤ_[2]) * toAdd (nu' (dmB 2 0)) + (0 : ℤ_[2]) * toAdd (nu' (dmD 2 0))
        + (-2 : ℤ_[2]) * toAdd (nu' (dmC 2 0))) = nu' (dmA 2 0)
      rw [hval]
      rfl
  · refine ⟨(1, 0, 0), Prod.ext ?_ ?_⟩
    · show GQ2.zpowZtwo GQ2.isProP_two_unitsPadicInt (-1 : ℤ_[2]ˣ) 1
          * GQ2.zpowZtwo GQ2.isProP_two_unitsPadicInt (mUnit 2) 0 = chiM 2 0 (dmB 2 0)
      rw [GQ2.zpowZtwo_one_exp, mpcNorm_zpowZtwo_zero, mul_one, chiM_dmB]
    · have hval : (1 : ℤ_[2]) * toAdd (nu' (dmB 2 0)) + (0 : ℤ_[2]) * toAdd (nu' (dmD 2 0))
          + (0 : ℤ_[2]) * toAdd (nu' (dmC 2 0)) = toAdd (nu' (dmB 2 0)) := by ring
      show ofAdd ((1 : ℤ_[2]) * toAdd (nu' (dmB 2 0)) + (0 : ℤ_[2]) * toAdd (nu' (dmD 2 0))
        + (0 : ℤ_[2]) * toAdd (nu' (dmC 2 0))) = nu' (dmB 2 0)
      rw [hval]
      rfl
  · refine ⟨(0, 0, 1), Prod.ext ?_ ?_⟩
    · show GQ2.zpowZtwo GQ2.isProP_two_unitsPadicInt (-1 : ℤ_[2]ˣ) 0
          * GQ2.zpowZtwo GQ2.isProP_two_unitsPadicInt (mUnit 2) 0 = chiM 2 0 (dmC 2 0)
      rw [mpcNorm_zpowZtwo_zero, mpcNorm_zpowZtwo_zero, one_mul, chiM_dmC]
    · have hval : (0 : ℤ_[2]) * toAdd (nu' (dmB 2 0)) + (0 : ℤ_[2]) * toAdd (nu' (dmD 2 0))
          + (1 : ℤ_[2]) * toAdd (nu' (dmC 2 0)) = toAdd (nu' (dmC 2 0)) := by ring
      show ofAdd ((0 : ℤ_[2]) * toAdd (nu' (dmB 2 0)) + (0 : ℤ_[2]) * toAdd (nu' (dmD 2 0))
        + (1 : ℤ_[2]) * toAdd (nu' (dmC 2 0))) = nu' (dmC 2 0)
      rw [hval]
      rfl
  · refine ⟨(0, 1, 0), Prod.ext ?_ ?_⟩
    · show GQ2.zpowZtwo GQ2.isProP_two_unitsPadicInt (-1 : ℤ_[2]ˣ) 0
          * GQ2.zpowZtwo GQ2.isProP_two_unitsPadicInt (mUnit 2) 1 = chiM 2 0 (dmD 2 0)
      rw [mpcNorm_zpowZtwo_zero, GQ2.zpowZtwo_one_exp, one_mul, chiM_dmD]
    · have hval : (0 : ℤ_[2]) * toAdd (nu' (dmB 2 0)) + (1 : ℤ_[2]) * toAdd (nu' (dmD 2 0))
          + (0 : ℤ_[2]) * toAdd (nu' (dmC 2 0)) = toAdd (nu' (dmD 2 0)) := by ring
      show ofAdd ((0 : ℤ_[2]) * toAdd (nu' (dmB 2 0)) + (1 : ℤ_[2]) * toAdd (nu' (dmD 2 0))
        + (0 : ℤ_[2]) * toAdd (nu' (dmC 2 0))) = nu' (dmD 2 0)
      rw [hval]
      rfl

end Span

/-! ## §2 The `ker χ_M` image, exactly

Wave 80 §3.3 displayed `ν'(ker χ_M) = ⟨ν'(C̄₀), 2·ν'(B̄)⟩` and reported it unavailable: it needs
the **structure** of `ℤ₂ˣ` as `⟨−1⟩ × (mUnit 2)^{ℤ₂}`, not merely its generation.  Wave 81's
`mpcNorm_free_unique` is that structure, so both inclusions are now theorems, at every marking of
`D_M 2 0` and with no level hypothesis. -/

section KerChi

variable (nu' : ContinuousMonoidHom (DM 2 0 : Type) (Multiplicative ℤ_[2]))

/-- **`⊆`**: every `ker χ_M` class has `ν'`-value in `ν'(C̄₀)·ℤ₂ + 2·ν'(B̄)·ℤ₂`.  The whole image
of `(χ_M, ν')` is trapped in §1's span (`mpcNorm_mem_of_gens`), and freeness reads off the
fibre over `1`: the `(−1)`-exponent is even and the `(mUnit 2)`-exponent vanishes. -/
theorem mpcPiv_kerChi_le {x : (DM 2 0 : Type)} (hx : chiM 2 0 x = 1) :
    ∃ m y : ℤ_[2],
      toAdd (nu' x) = m * toAdd (nu' (dmC 2 0)) + 2 * y * toAdd (nu' (dmB 2 0)) := by
  obtain ⟨⟨s, t, u⟩, hst⟩ := mpcNorm_mem_of_gens (mpcNorm_compPhi nu')
    (mpcPiv_isClosed_span _ _ _) (mpcPiv_gens_mem nu') x
  have hfst : GQ2.zpowZtwo GQ2.isProP_two_unitsPadicInt (-1 : ℤ_[2]ˣ) s
      * GQ2.zpowZtwo GQ2.isProP_two_unitsPadicInt (mUnit 2) t = 1 :=
    (congrArg Prod.fst hst).trans hx
  have hsnd : s * toAdd (nu' (dmB 2 0)) + t * toAdd (nu' (dmD 2 0))
      + u * toAdd (nu' (dmC 2 0)) = toAdd (nu' x) :=
    congrArg (fun q : ℤ_[2]ˣ × Multiplicative ℤ_[2] => toAdd q.2) hst
  obtain ⟨⟨y, hy⟩, rfl⟩ := mpcNorm_free_unique hfst
  exact ⟨u, y, by rw [hy] at hsnd; linear_combination -hsnd⟩

/-- **`⊇`**: every combination `m·ν'(C̄₀) + 2y·ν'(B̄)` is attained on `ker χ_M`, by the explicit
class `C̄₀^m·B̄^{2y}`. -/
theorem mpcPiv_kerChi_ge (m y : ℤ_[2]) :
    ∃ x : (DM 2 0 : Type), chiM 2 0 x = 1 ∧
      toAdd (nu' x) = m * toAdd (nu' (dmC 2 0)) + 2 * y * toAdd (nu' (dmB 2 0)) := by
  refine ⟨GQ2.zpowZtwo (isProP_DM 2 0) (dmC 2 0) m
      * GQ2.zpowZtwo (isProP_DM 2 0) (dmB 2 0) (2 * y), ?_, ?_⟩
  · rw [map_mul, GQ2.map_zpowZtwo (isProP_DM 2 0) GQ2.isProP_two_unitsPadicInt,
      GQ2.map_zpowZtwo (isProP_DM 2 0) GQ2.isProP_two_unitsPadicInt, chiM_dmC, chiM_dmB,
      mpcNorm_zpow_negOne_even ⟨y, rfl⟩, mul_one,
      SectionThree.zpowZtwo_of_sq_eq_one _ _ (one_pow 2), one_pow]
  · rw [map_mul, toAdd_mul, toAdd_map_zpowZtwo (isProP_DM 2 0) nu',
      toAdd_map_zpowZtwo (isProP_DM 2 0) nu']

end KerChi

/-! ## §3 What the level can and cannot do

The identity of §2 makes the two rows' asymmetry a one-line calculation rather than a hand
argument, in both directions. -/

section Exhaustion

variable (nu' : ContinuousMonoidHom (DM 2 0 : Type) (Multiplicative ℤ_[2]))

/-- **THE `ε = false` PIVOT, from the exact identity.**  Wave 81's `mpcNorm_pivot_of_even_dmB`
re-proved: with `ν'(B̄)` even, `2·ν'(B̄)` is in `4ℤ₂`, so a `ker χ_M` class of value `2` forces
`ν'(C̄₀)` to be a unit times `2`. -/
theorem mpcPiv_pivot_of_even_dmB
    (hC : ∃ c : ℤ_[2], toAdd (nu' (dmC 2 0)) = 2 * c)
    (hB : ∃ β : ℤ_[2], toAdd (nu' (dmB 2 0)) = 2 * β)
    (hex : ∃ x : (DM 2 0 : Type), chiM 2 0 x = 1 ∧ toAdd (nu' x) = 2) :
    ∃ γ : ℤ_[2]ˣ, toAdd (nu' (dmC 2 0)) = (γ : ℤ_[2]) * 2 ^ 1 := by
  obtain ⟨c, hc⟩ := hC
  obtain ⟨β, hβ⟩ := hB
  obtain ⟨x, hxchi, hxnu⟩ := hex
  rcases mpcRow_even_or_odd c with ⟨z, hz⟩ | ⟨w, hw⟩
  · exfalso
    obtain ⟨m, y, hmy⟩ := mpcPiv_kerChi_le nu' hxchi
    rw [hxnu, hc, hz, hβ] at hmy
    have hone : (2 : ℤ_[2]) * (2 * (m * z) + 2 * (y * β)) = 2 * 1 := by linear_combination -hmy
    have := mul_left_cancel₀ (by norm_num : (2 : ℤ_[2]) ≠ 0) hone
    exact mpcRow_not_even_and_odd (z := (1 : ℤ_[2])) ⟨m * z + y * β, by linear_combination -this⟩
      ⟨0, by ring⟩
  · refine ⟨(GQ2.isUnit_one_add_two_mul w).unit, ?_⟩
    rw [hc, hw, IsUnit.unit_spec, pow_one]
    ring

/-- **THE `ε = true` OBSTRUCTION, structurally.**  At `ν'(B̄)` odd the `ker χ_M` image is *all* of
`2ℤ₂` on the `B̄`-column alone, with no contribution from `ν'(C̄₀)`.  So the lower half of the
level (the input that discharges the `ε = false` pivot) is automatically satisfied on the
`ε = true` row and can never produce a contradiction there.  This is wave 80 §3.3's hand
counterexample `(−8, 1, 4, 1)` promoted from one marking to the whole technique: **no argument
that sees only the image of `(χ_M, ν')` decides the pivot**, because that image does not depend
on `ν'(C̄₀)` once `ν'(B̄)` is odd. -/
theorem mpcPiv_kerChi_full_of_odd_dmB (hB : ∃ β : ℤ_[2], toAdd (nu' (dmB 2 0)) = 1 + 2 * β)
    (z : ℤ_[2]) : ∃ x : (DM 2 0 : Type), chiM 2 0 x = 1 ∧ toAdd (nu' x) = 2 * z := by
  obtain ⟨β, hβ⟩ := hB
  obtain ⟨y, hy⟩ := (GQ2.isUnit_one_add_two_mul β).exists_left_inv
  obtain ⟨x, hxchi, hxnu⟩ := mpcPiv_kerChi_ge nu' 0 (y * z)
  refine ⟨x, hxchi, ?_⟩
  rw [hxnu, hβ]
  calc (0 : ℤ_[2]) * toAdd (nu' (dmC 2 0)) + 2 * (y * z) * (1 + 2 * β)
      = 2 * z * (y * (1 + 2 * β)) := by ring
    _ = 2 * z := by rw [hy, mul_one]

end Exhaustion

/-! ## §4 The pivot is an orbit question, and nothing else

`fieldId_chosenEquivM_sqrtNegTen` is a `Nonempty.some`: nothing is known about it beyond
orientation.  So a pivot statement at *that* equivalence is either true at every oriented
equivalence or unprovable, and the honest target is the pivot at **some** oriented equivalence,
which is what the branch datum consumes.  The two are related by exactly one fact: oriented
equivalences form a torsor under the χ-preserving automorphisms of `D_M`. -/

section Orbit

variable {K : IntermediateField ℚ_[2] ℚ̄₂} [FiniteDimensional ℚ_[2] K]
  [CompactSpace (GalK K)] [TotallyDisconnectedSpace (GalK K)] {Rec : LocalReciprocity}
  {alpha : ℕ}

omit [FiniteDimensional ℚ_[2] K] in
/-- **Oriented equivalences form a torsor under `Aut_χ(D_M)`.**  `e' ∘ e⁻¹` read on the core. -/
theorem mpcPiv_transport (e e' : OrientedContinuousMulEquiv (chiM alpha 0)
    (chiCycKTwo (K := K))) (x : (DM alpha 0 : Type)) :
    chiM alpha 0 (e.1.symm (e'.1 x)) = chiM alpha 0 x := by
  have h : chiCycKTwo (K := K) (e.1 (e.1.symm (e'.1 x))) = chiM alpha 0 (e.1.symm (e'.1 x)) :=
    e.2 _
  rw [e.1.apply_symm_apply] at h
  exact h.symm.trans (e'.2 x)

/-- Precomposing an oriented equivalence with a χ-preserving automorphism is oriented. -/
def mpcPiv_comp (e : OrientedContinuousMulEquiv (chiM alpha 0) (chiCycKTwo (K := K)))
    (Psi : ContinuousMulEquiv (DM alpha 0 : Type) (DM alpha 0 : Type))
    (hPsi : ∀ x, chiM alpha 0 (Psi x) = chiM alpha 0 x) :
    OrientedContinuousMulEquiv (chiM alpha 0) (chiCycKTwo (K := K)) :=
  ⟨Psi.trans e.1, fun x => (e.2 (Psi x)).trans (hPsi x)⟩

@[simp] theorem mpcPiv_nuPullback_comp (B : MarkedRecip Rec K)
    (e : OrientedContinuousMulEquiv (chiM alpha 0) (chiCycKTwo (K := K)))
    (Psi : ContinuousMulEquiv (DM alpha 0 : Type) (DM alpha 0 : Type))
    (hPsi : ∀ x, chiM alpha 0 (Psi x) = chiM alpha 0 x) (x : (DM alpha 0 : Type)) :
    fieldUni_nuPullbackM B (mpcPiv_comp e Psi hPsi) x = fieldUni_nuPullbackM B e (Psi x) := rfl

/-- **THE PIVOT, AS AN ORBIT STATEMENT.**  Both implications.  The left side is what the branch
datum consumes; the right side mentions only `D_M 2 0`, its orientation, and the one marking
transported along the chosen equivalence.  So the `√−10` pivot is neither more nor less than:
*does the χ-preserving orbit of `C̄₀` reach `ν`-valuation one?* -/
theorem mpcPiv_pivot_iff_orbit (B : MarkedRecip Rec K)
    (e : OrientedContinuousMulEquiv (chiM alpha 0) (chiCycKTwo (K := K))) {r : ℕ} :
    (∃ e' : OrientedContinuousMulEquiv (chiM alpha 0) (chiCycKTwo (K := K)),
        ∃ γ : ℤ_[2]ˣ, toAdd (fieldUni_nuPullbackM B e' (dmC alpha 0)) = (γ : ℤ_[2]) * 2 ^ r) ↔
      ∃ Psi : ContinuousMulEquiv (DM alpha 0 : Type) (DM alpha 0 : Type),
        (∀ x, chiM alpha 0 (Psi x) = chiM alpha 0 x) ∧
          ∃ γ : ℤ_[2]ˣ,
            toAdd (fieldUni_nuPullbackM B e (Psi (dmC alpha 0))) = (γ : ℤ_[2]) * 2 ^ r := by
  constructor
  · rintro ⟨e', γ, hγ⟩
    refine ⟨e'.1.trans e.1.symm, fun x => mpcPiv_transport e e' x, γ, ?_⟩
    show toAdd (nuUrKTwo B (e.1 (e.1.symm (e'.1 (dmC alpha 0))))) = _
    rw [e.1.apply_symm_apply]
    exact hγ
  · rintro ⟨Psi, hPsi, γ, hγ⟩
    exact ⟨mpcPiv_comp e Psi hPsi, γ, hγ⟩

end Orbit

/-! ## §5 The named residual: MC1 §5.3's `M6` at parameter one

`docs/dyadic/mc-design.md:211` lists the family

    M6 :  `Y_c : C̄₀ ↦ B̄^{2c₁}·C̄₀`,   `c₁ ∈ ℤ₂`,

in the S3 block.  Its ν-frame action is `ν'(C̄₀) ↦ ν'(C̄₀) + 2c₁·ν'(B̄)`, and the exponent `2c₁` is
forced: χ-preservation needs `χ_M(B̄)^{c} = 1`, i.e. an even power of `B̄`, since `χ_M(B̄) = −1`.
That is exactly the direction §3 shows the level cannot see, and, by §4, the only thing between
the tree and the `√−10` row. -/

section Shift

/-- **`M6` at parameter one**, in ν-frame form: a χ-preserving automorphism of `D_M α 0` that
moves the pivot row by twice the `B̄`-row, on every marking at once. -/
def MpcPivShift (alpha : ℕ) : Prop :=
  ∃ Psi : ContinuousMulEquiv (DM alpha 0 : Type) (DM alpha 0 : Type),
    (∀ x, chiM alpha 0 (Psi x) = chiM alpha 0 x) ∧
      ∀ f : ContinuousMonoidHom (DM alpha 0 : Type) (Multiplicative ℤ_[2]),
        toAdd (f (Psi (dmC alpha 0))) = toAdd (f (dmC alpha 0)) + 2 * toAdd (f (dmB alpha 0))

/-- **The shift discharges the pivot on any `ε = true` marking.**  Case on the parity of
`ν'(C̄₀)/2`: if it is odd the marking already has the pivot, and if it is even one application of
`M6` adds `2·ν'(B̄)` with `ν'(B̄)` odd, which lands on valuation exactly one.  So a *single*
parameter of the family suffices; the whole `ℤ₂`-family is not needed. -/
theorem mpcPiv_orbit_of_shift (hshift : MpcPivShift 2)
    (nu' : ContinuousMonoidHom (DM 2 0 : Type) (Multiplicative ℤ_[2]))
    (hC : ∃ c : ℤ_[2], toAdd (nu' (dmC 2 0)) = 2 * c)
    (hB : ∃ β : ℤ_[2], toAdd (nu' (dmB 2 0)) = 1 + 2 * β) :
    ∃ Psi : ContinuousMulEquiv (DM 2 0 : Type) (DM 2 0 : Type),
      (∀ x, chiM 2 0 (Psi x) = chiM 2 0 x) ∧
        ∃ γ : ℤ_[2]ˣ, toAdd (nu' (Psi (dmC 2 0))) = (γ : ℤ_[2]) * 2 ^ 1 := by
  obtain ⟨c, hc⟩ := hC
  obtain ⟨β, hβ⟩ := hB
  rcases mpcRow_even_or_odd c with ⟨z, hz⟩ | ⟨w, hw⟩
  · obtain ⟨Psi, hchi, hrow⟩ := hshift
    refine ⟨Psi, hchi, (GQ2.isUnit_one_add_two_mul (z + β)).unit, ?_⟩
    rw [hrow nu', hc, hz, hβ, IsUnit.unit_spec, pow_one]
    ring
  · exact ⟨ContinuousMulEquiv.refl _, fun _ => rfl, (GQ2.isUnit_one_add_two_mul w).unit,
      by rw [show (ContinuousMulEquiv.refl (DM 2 0 : Type)) (dmC 2 0) = dmC 2 0 from rfl, hc, hw,
        IsUnit.unit_spec, pow_one]; ring⟩

/-- **The orbit of `C̄₀` has exactly one free direction.**  `mpcPiv_kerChi_le` at `Ψ(C̄₀)`, which
lies in `ker χ_M` because `Ψ` preserves `χ_M` and `χ_M(C̄₀) = 1`: *every* χ-preserving
automorphism moves the pivot row inside `ν'(C̄₀)·ℤ₂ + 2·ν'(B̄)·ℤ₂`.  The first summand is M3
scaling, which the tree has; the second is `M6`, which it does not. -/
theorem mpcPiv_orbit_shape (nu' : ContinuousMonoidHom (DM 2 0 : Type) (Multiplicative ℤ_[2]))
    (Psi : ContinuousMulEquiv (DM 2 0 : Type) (DM 2 0 : Type))
    (hPsi : ∀ x, chiM 2 0 (Psi x) = chiM 2 0 x) :
    ∃ m y : ℤ_[2], toAdd (nu' (Psi (dmC 2 0)))
      = m * toAdd (nu' (dmC 2 0)) + 2 * y * toAdd (nu' (dmB 2 0)) :=
  mpcPiv_kerChi_le nu' (by rw [hPsi]; exact chiM_dmC 2 0)

/-- **`M6` IS NECESSARY, NOT MERELY SUFFICIENT.**  Suppose the marking misses the pivot outright
(`ν'(C̄₀) ∈ 4ℤ₂`) on an `ε = true` row (`ν'(B̄)` odd).  Then any χ-preserving automorphism that
*does* achieve the pivot has an **odd** `B̄`-coefficient on its `C̄₀`-row: it is `M6` at an odd
parameter, composed with whatever the tree already has.  Together with `mpcPiv_orbit_of_shift`
this pins the residual exactly: the `√−10` row lands if and only if the `M6` direction is
available at some odd parameter. -/
theorem mpcPiv_shift_necessary (nu' : ContinuousMonoidHom (DM 2 0 : Type) (Multiplicative ℤ_[2]))
    {z β : ℤ_[2]} (hC : toAdd (nu' (dmC 2 0)) = 4 * z)
    (hB : toAdd (nu' (dmB 2 0)) = 1 + 2 * β)
    (Psi : ContinuousMulEquiv (DM 2 0 : Type) (DM 2 0 : Type))
    (hPsi : ∀ x, chiM 2 0 (Psi x) = chiM 2 0 x)
    (hpiv : ∃ γ : ℤ_[2]ˣ, toAdd (nu' (Psi (dmC 2 0))) = (γ : ℤ_[2]) * 2 ^ 1) :
    ∃ m y w : ℤ_[2], toAdd (nu' (Psi (dmC 2 0)))
        = m * toAdd (nu' (dmC 2 0)) + 2 * y * toAdd (nu' (dmB 2 0)) ∧ y = 1 + 2 * w := by
  obtain ⟨γ, hγ⟩ := hpiv
  obtain ⟨m, y, hmy⟩ := mpcPiv_orbit_shape nu' Psi hPsi
  refine ⟨m, y, ?_⟩
  rcases mpcRow_even_or_odd y with ⟨y', hy'⟩ | ⟨w, hw⟩
  · exfalso
    rw [hγ, hC, hB, hy'] at hmy
    have h2 : (2 : ℤ_[2]) * (γ : ℤ_[2])
        = 2 * (2 * (m * z) + 2 * y' + 4 * (y' * β)) := by linear_combination hmy
    have hcancel := mul_left_cancel₀ (by norm_num : (2 : ℤ_[2]) ≠ 0) h2
    have hval : (γ : ℤ_[2]) * 2 ^ 0 = 2 ^ 1 * (m * z + y' + 2 * (y' * β)) := by
      rw [pow_zero, mul_one, pow_one]
      linear_combination hcancel
    exact absurd (mpcCert_le_of_two_pow_eq γ.isUnit hval) (by omega)
  · exact ⟨w, hmy, hw⟩

end Shift

/-! ## §6 The two `√−10` statements

The first is the honest one: the branch datum **at the row's own canonical marking**, over
`MpcPivShift` and nothing else.  The second is the acceptance statement, and it needs no clause
at all, for a reason that has nothing to do with the pivot.  Read the warning. -/

section SqrtNegTen

variable [CompactSpace AbsGalQ2] [TotallyDisconnectedSpace AbsGalQ2] {R : LocalReciprocity}
  [T2Space (GalK KSqrtNegTen)]

omit [T2Space (GalK KSqrtNegTen)] in
/-- The `√−10` marking is even at `C̄₀` (the level) and odd at `B̄` (`λ(−1) = 1`), at every
oriented equivalence. -/
theorem mpcPiv_rows_sqrtNegTen (B : MarkedRecip R KSqrtNegTen)
    (e : OrientedContinuousMulEquiv (chiM 2 0) (chiCycKTwo (K := KSqrtNegTen))) :
    (∃ c : ℤ_[2], toAdd (fieldUni_nuPullbackM B e (dmC 2 0)) = 2 * c) ∧
      ∃ β : ℤ_[2], toAdd (fieldUni_nuPullbackM B e (dmB 2 0)) = 1 + 2 * β := by
  refine ⟨?_, ?_⟩
  · obtain ⟨y, hy⟩ := mpcCert_chiKerLevel_of_level B (mpcNorm_level_sqrtNegTen B) e
      (dmC 2 0) (chiM_dmC 2 0)
    exact ⟨y, by rw [hy, pow_one]⟩
  · exact mpcRow_congr_of_lambda e (mpcNorm_lambdaOne_negOne_sqrtNegTen B) (chiM_dmB 2 0)

/-- **THE `√−10` BRANCH DATUM AT THE ROW'S CANONICAL MARKING, OVER `MpcPivShift` ALONE.**  Every
other input of wave 81 is now a theorem: the level (`mpcNorm_level_sqrtNegTen`), `λ(−1) = 1` and
`λ(5) = 1` (`mpcNorm_lambdaOne_*_sqrtNegTen`), and the marking triple is discharged at `mpcNu`.
So the whole `ε = true` row costs exactly one abstract move on `D_M 2 0`, uniform in the field
and free of arithmetic. -/
theorem mpcPiv_genAsmBranch_sqrtNegTen_of_shift (hshift : MpcPivShift 2)
    (B : MarkedRecip R KSqrtNegTen) :
    ∃ G : GenAsmBranch KSqrtNegTen B, G.pres = .Mpc 2 1 true .one 0 := by
  obtain ⟨hC, hB⟩ := mpcPiv_rows_sqrtNegTen B (fieldId_chosenEquivM_sqrtNegTen B)
  obtain ⟨Psi, hchi, γ, hγ⟩ := mpcPiv_orbit_of_shift hshift _ hC hB
  set e := mpcPiv_comp (fieldId_chosenEquivM_sqrtNegTen B) Psi hchi with he
  -- [W83-RECORDS: the producer now also names the marking `mpcNu 2 1 (p true 1)`; this
  -- statement keeps the weaker form and drops the conjunct here.]
  refine Exists.imp (fun _ hG => hG.1)
    (mpcCert_genAsmBranch_of_orientedMpc 1 (p true 1) true .one (le_refl 2) (by omega)
      (by rw [finrank_KSqrtNegTen]; rfl) e
      (mpcCert_chiKerLevel_of_level B (mpcNorm_level_sqrtNegTen B) e) ⟨⟨γ, hγ⟩, ?_, ?_⟩)
  · obtain ⟨y, hy⟩ := mpcRow_congr_of_lambda e (mpcNorm_lambdaOne_mUnit_sqrtNegTen B)
      (chiM_dmD 2 0)
    exact ⟨y, by rw [hy, pow_one]⟩
  · obtain ⟨y, hy⟩ := mpcRow_congr_of_lambda e (mpcNorm_lambdaOne_negOne_sqrtNegTen B)
      (chiM_dmB 2 0)
    exact ⟨y, by rw [hy, pow_one]; norm_num⟩

/-- The transported marking, retyped at the `Ztwo` spelling the branch record uses. -/
def mpcPiv_nuZtwo {K : IntermediateField ℚ_[2] ℚ̄₂} [FiniteDimensional ℚ_[2] K] {alpha : ℕ}
    (nu' : ContinuousMonoidHom (DM alpha 0 : Type) (Multiplicative ℤ_[2])) :
    ContinuousMonoidHom (DM alpha 0 : Type) Ztwo where
  toFun x := ztwoIota.symm (nu' x)
  map_one' := by rw [map_one, map_one]
  map_mul' x y := by rw [map_mul, map_mul]
  continuous_toFun := ztwoIota.symm.continuous_toFun.comp nu'.continuous_toFun

/-- **THE ACCEPTANCE STATEMENT, WITH NO CLAUSE, AND A WARNING.**

⚠ This is *not* the pivot.  `GenAsmBranch` stores `nuP` as "a construction, not an obligation"
(`GeneralAssembly.lean:212`) and `MarkedCoreRealization` carries no orientation clause, so the
record's whole content at a fixed row is: the degree, plus a topological-group equivalence
`genAsmCore pres ≃ G_K(2)`, plus *some* surjective marking compatible with `ν_ur` along it.  The
transported marking is such a marking by construction, and wave 77's range identity supplies the
equivalence, so no arithmetic is needed.

What this branch datum does **not** carry is that the marking is the row's canonical `mpcNu 2 1 1`.
That is what `GenAsmRowResidual.cand` needs, since the committed producer at this row is
`Instances.MProcyclicCore.mpcWordCertificate α r p q` at that marking, and equally what the three
`Matches` conditions of `FieldBranchSelector` read.  For the tied statement use
`mpcPiv_genAsmBranch_sqrtNegTen_of_shift`. -/
theorem mpcPiv_genAsmBranch_sqrtNegTen (B : MarkedRecip R KSqrtNegTen) :
    ∃ G : GenAsmBranch KSqrtNegTen B, G.pres = .Mpc 2 1 true .one 0 := by
  set e := fieldId_chosenEquivM_sqrtNegTen B with he
  refine ⟨{ pres := .Mpc 2 1 true .one 0
            hdeg := by rw [finrank_KSqrtNegTen]; rfl
            nuP := mpcPiv_nuZtwo (K := KSqrtNegTen) (fieldUni_nuPullbackM B e)
            hnuP := ?_
            realization := { equiv := e.1, nu_equiv := fun x => ztwoIota.apply_symm_apply _ } },
    rfl⟩
  intro z
  obtain ⟨x, hx⟩ := mpcRow_surjective_nuPullbackM B e
    (mpcRow_surjective_nu_ur_quadField not_isSquare_neg_ten mpcRow_valuation_neg_ten_odd
      mpcRow_norm_neg_ten B) (ztwoIota z)
  exact ⟨x, by
    show ztwoIota.symm (fieldUni_nuPullbackM B e x) = z
    rw [hx, ztwoIota.symm_apply_apply]⟩

end SqrtNegTen

/-! ## §7 Axiom pins

One line per declaration, in declaration order, measured against the mirror.  Three sets occur,
all already committed; **this lane introduces no axiom**.

* **The standard three** (`propext`, `Classical.choice`, `Quot.sound`) on all of §1 through §5
  and on `mpcPiv_rows_sqrtNegTen`: the exact `ker χ_M` image, the orbit equivalence and the shift
  criterion are pure `D_M`/`ℤ₂ˣ` statements and cost nothing.
* **Plus the even route's endpoint set** (`hilbertSymbol_normCriterion_finiteDyadic`,
  `tateDualityAt`, `Foundations.absGalQ2_isTopologicallyFinitelyGenerated`,
  `Foundations.absGalQ2_localEulerCharacteristic`) on the acceptance statement
  `mpcPiv_genAsmBranch_sqrtNegTen`, through `fieldId_chosenEquivM_sqrtNegTen`.
* **Plus `peripheralCyclotomicAction`** on `mpcPiv_genAsmBranch_sqrtNegTen_of_shift`, which is
  wave 81's set on `mpcNorm_genAsmBranch_sqrtNegTen_of_pivot` exactly.  The gap between the two
  bullets is itself informative: `peripheralCyclotomicAction` (B8) enters only through
  `mpcCert_markedMatching`'s M3 scaling row, i.e. only through *normalizing* the marking.  The
  untied datum of §6 never normalizes, so it is strictly cheaper in axioms as well as strictly
  weaker in content. -/

section AxiomPins

#print axioms mpcPiv_span
#print axioms mpcPiv_isClosed_span
#print axioms mpcPiv_gens_mem
#print axioms mpcPiv_kerChi_le
#print axioms mpcPiv_kerChi_ge
#print axioms mpcPiv_pivot_of_even_dmB
#print axioms mpcPiv_kerChi_full_of_odd_dmB
#print axioms mpcPiv_transport
#print axioms mpcPiv_comp
#print axioms mpcPiv_nuPullback_comp
#print axioms mpcPiv_pivot_iff_orbit
#print axioms MpcPivShift
#print axioms mpcPiv_orbit_of_shift
#print axioms mpcPiv_orbit_shape
#print axioms mpcPiv_shift_necessary
#print axioms mpcPiv_rows_sqrtNegTen
#print axioms mpcPiv_genAsmBranch_sqrtNegTen_of_shift
#print axioms mpcPiv_nuZtwo
#print axioms mpcPiv_genAsmBranch_sqrtNegTen

end AxiomPins

end

end GQ2.Dyadic.Instances.MpcPiv
