/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Opus-4.8 and Fable-5
-/
module

public import Mathlib.RingTheory.Trace.Basic
public import GQ2.StiefelWhitney
public import GQ2.KummerKrullBridge

@[expose] public section

/-!
# Twisted trace forms of dyadic quadratic extensions (B9-A, node N3) and the draft axiom

Second layer of the B9-A plan (`docs/orchestration/b9a-proof-plan.md`): the quadratic extension
`k(δ)/k`, the `a`-twisted trace forms `Tr_{k(δ)/k}⟨a⟩`, and — in the clearly marked final
section — the **draft statement** of the replacement axiom `relativeStiefelWhitney_dyadic`,
kept here as a sorried `theorem` until the owner signs off (ticket T5 moves it to
`GQ2/Foundations/Axioms.lean`).

## The field construction (L-encoding decision, `docs/orchestration/b9a-t1-design.md`)

`L` is `quadExt k δ := IntermediateField.adjoin ↥k {δ}`, the adjoin over `↥k` inside `ℚ̄₂`.
No ambient `L : IntermediateField ℚ_[2] ℚ̄₂` is carried: the subgroup side of the axiom (the
`hidx`/`hUo` stabilizer encoding, reused verbatim from B9) and the field side are parametrized
by the *same* `δ`, so their compatibility is provable rather than hypothesized
(`GQ2/KummerKrullBridge.lean` machinery; see `finrank_quadExt_eq_two`).  All trace/finrank API
applies because `quadExt k δ` is an intermediate field of `ℚ̄₂/↥k`: `Algebra ↥k ↥(quadExt k δ)`
and `Algebra.trace ↥k ↥(quadExt k δ)` are found by instance search, and finite-dimensionality
over `↥k` follows from integrality of `δ` (`finiteDimensional_quadExt`).

## Contents

* `quadExt k δ` — the extension `k(δ)` of `↥k`; `isIntegral_of_sq_eq`,
  `finiteDimensional_quadExt` (proved).
* `finrank_quadExt_eq_two` — `[k(δ) : k] = 2` from the B9 index-2 stabilizer hypothesis
  (sorried; ticket T2 via `KummerKrullBridge.exists_quadratic_of_open_index_two`).
* `traceFormOne k δ` — `Tr⟨1⟩ : z ↦ Tr_{k(δ)/k}(z·z)`; `traceFormTwisted k δ a` —
  `Tr⟨a⟩ : z ↦ Tr_{k(δ)/k}(a·z·z)`.  Both are genuine `QuadraticForm ↥k ↥(quadExt k δ)`
  definitions (no sorries), built from `Algebra.traceForm` via
  `LinearMap.BilinMap.toQuadraticMap`.
* `traceFormOne_isDiagonalization`, `traceFormTwisted_isDiagonalization` — Lemma 6.16's
  diagonalizations `Tr⟨1⟩ ≃ ⟨2, 2d⟩` and `Tr⟨a⟩ ≃ ⟨2u, 2dn/u⟩` for `a = u + vδ`
  (sorried; ticket T2, basis `{1, δ}` and completing the square with `u ∈ kˣ`).
* `relativeStiefelWhitney_dyadic` — the draft axiom statement (sorried; ticket T5).

## Citations

Kahn, Invent. Math. 78 (1984), Théorème 2; Evens, Trans. AMS 108 (1963), Thm 1; Kozlowski,
Proc. AMS 91 (1984), Thm 1.1.  Paper: §6, eq. (111), Lemmas 6.13/6.16.
-/

namespace GQ2

-- Same relaxation as `GQ2/StiefelWhitney.lean`: the trace-form and quadratic-form instance
-- chains resolve through the `IntermediateField` instance space.
set_option synthInstance.maxHeartbeats 400000

local notation "ℚ̄₂" => AlgebraicClosure ℚ_[2]

section TraceForms

variable (k : IntermediateField ℚ_[2] ℚ̄₂)

/-- The extension `k(δ)` of the finite dyadic base `k`, as an intermediate field of `ℚ̄₂/↥k`.
For the B9-A setting `δ² = d ∈ kˣ` with `d` a nonsquare, this is the quadratic extension `L`
of the Evens–Kahn identity; the degree-2 fact is `finrank_quadExt_eq_two`. -/
noncomputable def quadExt (δ : ℚ̄₂) : IntermediateField ↥k ℚ̄₂ :=
  IntermediateField.adjoin ↥k {δ}

/-- A square root of an element of `k` is integral over `↥k` (monic witness `X² − d`). -/
theorem isIntegral_of_sq_eq (d : (↥k)ˣ) {δ : ℚ̄₂} (hδ : δ ^ 2 = ((d : ↥k) : ℚ̄₂)) :
    IsIntegral ↥k δ :=
  ⟨Polynomial.X ^ 2 - Polynomial.C (d : ↥k),
    Polynomial.monic_X_pow_sub_C _ two_ne_zero, by simp [hδ]⟩

/-- `k(δ)` is a finite extension of `↥k` when `δ² ∈ k` — the instance input for the trace
form's nondegeneracy (`Algebra.traceForm_nondegenerate`, char 0 so separability is free). -/
theorem finiteDimensional_quadExt (d : (↥k)ˣ) {δ : ℚ̄₂} (hδ : δ ^ 2 = ((d : ↥k) : ℚ̄₂)) :
    FiniteDimensional ↥k ↥(quadExt k δ) :=
  IntermediateField.adjoin.finiteDimensional (isIntegral_of_sq_eq k d hδ)

/-- **`[k(δ) : k] = 2` from the B9 subgroup encoding**: if the stabilizer of `δ` meets
`G_k = k.fixingSubgroup` in an open subgroup of index 2, then `quadExt k δ` is quadratic
over `↥k`.  This is the bridge that lets the draft axiom's field-level hypothesis `hdeg` be
discharged from the verbatim B9 hypotheses `hUo`/`hidx` at the flip (plan node N3, risk R2). -/
theorem finrank_quadExt_eq_two [FiniteDimensional ℚ_[2] k] (d : (↥k)ˣ) {δ : ℚ̄₂}
    (hδ : δ ^ 2 = ((d : ↥k) : ℚ̄₂))
    (hidx : ((MulAction.stabilizer (Kummer.GaloisGroup ℚ_[2]) δ).subgroupOf
        k.fixingSubgroup).index = 2)
    (hUo : IsOpen (((MulAction.stabilizer (Kummer.GaloisGroup ℚ_[2]) δ).subgroupOf
        k.fixingSubgroup : Subgroup k.fixingSubgroup) : Set k.fixingSubgroup)) :
    Module.finrank ↥k ↥(quadExt k δ) = 2 := by
  -- Krull bridge: the open index-2 stabilizer cuts out a quadratic subextension `L`.
  obtain ⟨L, hkL, _hFinL, hsubEq, hdeg2⟩ := KummerSurjectivity.exists_quadratic_of_open_index_two k
    ((MulAction.stabilizer (Kummer.GaloisGroup ℚ_[2]) δ).subgroupOf k.fixingSubgroup) hUo hidx
  -- `δ ∈ L`: any `φ ∈ L.fixingSubgroup` also fixes `k` (as `k ≤ L`), hence lies in the stabilizer
  -- of `δ` (`hsubEq`), so fixes `δ`; and `L` is the fixed field of `L.fixingSubgroup` (Krull).
  have hδL : δ ∈ L := by
    have hin : δ ∈ IntermediateField.fixedField L.fixingSubgroup := by
      rw [IntermediateField.mem_fixedField_iff]
      intro φ hφ
      have hφk : φ ∈ k.fixingSubgroup :=
        (IntermediateField.mem_fixingSubgroup_iff k φ).mpr fun x hx =>
          (IntermediateField.mem_fixingSubgroup_iff L φ).mp hφ x (hkL hx)
      have hmem : (⟨φ, hφk⟩ : k.fixingSubgroup)
          ∈ (MulAction.stabilizer (Kummer.GaloisGroup ℚ_[2]) δ).subgroupOf k.fixingSubgroup := by
        rw [← hsubEq, Subgroup.mem_subgroupOf]; exact hφ
      rw [Subgroup.mem_subgroupOf, MulAction.mem_stabilizer_iff] at hmem
      exact hmem
    rwa [InfiniteGalois.fixedField_fixingSubgroup L] at hin
  -- `δ ∉ k`: else every element of `G_k` fixes `δ`, making the stabilizer `⊤` (index 1 ≠ 2).
  have hδbot : δ ∉ (⊥ : IntermediateField ↥k ℚ̄₂) := by
    intro hmem
    obtain ⟨y, hy⟩ := IntermediateField.mem_bot.mp hmem
    have htop : (MulAction.stabilizer (Kummer.GaloisGroup ℚ_[2]) δ).subgroupOf
        k.fixingSubgroup = ⊤ := by
      rw [Subgroup.eq_top_iff']
      intro g
      rw [Subgroup.mem_subgroupOf, MulAction.mem_stabilizer_iff, AlgEquiv.smul_def, ← hy]
      exact (IntermediateField.mem_fixingSubgroup_iff k _).mp g.2 _ y.2
    rw [htop, Subgroup.index_top] at hidx
    exact absurd hidx (by norm_num)
  -- `k(δ) = L` (both quadratic over `k`), so `[k(δ):k] = [L:k] = 2`.  Degree ≥ 2 from `δ ∉ k`,
  -- and `k(δ) ≤ L` from `δ ∈ L`, forces equality with the degree-2 bridge extension.
  have hint : IsIntegral ↥k δ := isIntegral_of_sq_eq k d hδ
  have hfr : Module.finrank ↥k ↥(quadExt k δ) = (minpoly ↥k δ).natDegree :=
    IntermediateField.adjoin.finrank hint
  have h2le : 2 ≤ Module.finrank ↥k ↥(quadExt k δ) := by
    have hne1 : (minpoly ↥k δ).natDegree ≠ 1 := fun h1 =>
      hδbot (IntermediateField.finrank_adjoin_simple_eq_one_iff.mp (hfr.trans h1))
    have hge1 : 1 ≤ (minpoly ↥k δ).natDegree := minpoly.natDegree_pos hint
    omega
  haveI : FiniteDimensional ↥k ↥(IntermediateField.extendScalars hkL) :=
    Module.finite_of_finrank_pos (by rw [hdeg2]; norm_num)
  have hle : quadExt k δ ≤ IntermediateField.extendScalars hkL :=
    IntermediateField.adjoin_simple_le_iff.mpr ((IntermediateField.mem_extendScalars hkL).mpr hδL)
  rw [IntermediateField.eq_of_le_of_finrank_le hle (by rw [hdeg2]; exact h2le), hdeg2]

/-- The **untwisted trace form** `Tr⟨1⟩` of `k(δ)/k`: the quadratic form
`z ↦ Tr_{k(δ)/k}(z·z)` over `↥k`, i.e. `Algebra.traceForm` read as a quadratic map. -/
noncomputable def traceFormOne (δ : ℚ̄₂) : QuadraticForm ↥k ↥(quadExt k δ) :=
  LinearMap.BilinMap.toQuadraticMap (Algebra.traceForm ↥k ↥(quadExt k δ))

@[simp] lemma traceFormOne_apply (δ : ℚ̄₂) (z : ↥(quadExt k δ)) :
    traceFormOne k δ z = Algebra.trace ↥k ↥(quadExt k δ) (z * z) := by
  simp [traceFormOne, Algebra.traceForm_apply]

/-- The **`a`-twisted trace form** `Tr⟨a⟩` of `k(δ)/k`: the quadratic form
`z ↦ Tr_{k(δ)/k}(a·z·z)` over `↥k`, from the twisted bilinear form
`(z, w) ↦ Tr(a·z·w)`.  For `a ∈ k(δ)ˣ` this is Kahn's transfer `Tr_{L/k}⟨a⟩` of the rank-1
form `⟨a⟩`. -/
noncomputable def traceFormTwisted (δ : ℚ̄₂) (a : ↥(quadExt k δ)) :
    QuadraticForm ↥k ↥(quadExt k δ) :=
  LinearMap.BilinMap.toQuadraticMap
    ((Algebra.traceForm ↥k ↥(quadExt k δ)).compl₁₂ (LinearMap.mulLeft ↥k a) LinearMap.id)

@[simp] lemma traceFormTwisted_apply (δ : ℚ̄₂) (a z : ↥(quadExt k δ)) :
    traceFormTwisted k δ a z = Algebra.trace ↥k ↥(quadExt k δ) (a * z * z) := by
  simp [traceFormTwisted, Algebra.traceForm_apply]

/-- **Lemma 6.16, first diagonalization**: `Tr⟨1⟩ ≃ ⟨2, 2d⟩` over the basis `{1, δ}`
(Gram matrix `diag(Tr 1, Tr δ²) = diag(2, 2d)`). -/
theorem traceFormOne_isDiagonalization (d : (↥k)ˣ) {δ : ℚ̄₂}
    (hδ : δ ^ 2 = ((d : ↥k) : ℚ̄₂)) (hdeg : Module.finrank ↥k ↥(quadExt k δ) = 2) :
    IsDiagonalization k (traceFormOne k δ) (twoUnit k) (twoUnit k * d) := by
  have hint : IsIntegral ↥k δ := isIntegral_of_sq_eq k d hδ
  set δ' : ↥(quadExt k δ) := IntermediateField.AdjoinSimple.gen ↥k δ with hδ'def
  have hcoe : (δ' : ℚ̄₂) = δ := IntermediateField.AdjoinSimple.coe_gen ↥k δ
  -- `δ ∉ k` (else the extension would be trivial, contradicting `hdeg`).
  have hδbot : δ ∉ (⊥ : IntermediateField ↥k ℚ̄₂) := fun hmem => by
    have : Module.finrank ↥k ↥(quadExt k δ) = 1 :=
      IntermediateField.finrank_adjoin_simple_eq_one_iff.mpr hmem
    omega
  -- The Gram data on the basis `{1, δ'}`: `δ'² = d`, `Tr δ' = 0`, `Tr 1 = 2`, `Tr δ'² = 2d`.
  have hδ'sq : δ' * δ' = algebraMap ↥k ↥(quadExt k δ) (d : ↥k) := by
    apply Subtype.ext
    rw [IntermediateField.coe_algebraMap_apply]
    push_cast [hcoe]
    rw [← pow_two]; exact hδ
  have hnext : (minpoly ↥k δ).nextCoeff = 0 := by
    have hdvd : minpoly ↥k δ ∣ Polynomial.X ^ 2 - Polynomial.C (d : ↥k) :=
      minpoly.dvd ↥k δ (by simp [hδ])
    have hmonic_q : (Polynomial.X ^ 2 - Polynomial.C (d : ↥k)).Monic :=
      Polynomial.monic_X_pow_sub_C _ two_ne_zero
    have hdeg_m : (minpoly ↥k δ).natDegree = 2 :=
      (IntermediateField.adjoin.finrank hint).symm.trans hdeg
    have hmp : minpoly ↥k δ = Polynomial.X ^ 2 - Polynomial.C (d : ↥k) :=
      (Polynomial.eq_of_monic_of_dvd_of_natDegree_le (minpoly.monic hint) hmonic_q hdvd
        (by rw [Polynomial.natDegree_X_pow_sub_C]; omega)).symm
    rw [hmp, Polynomial.nextCoeff]
    simp [Polynomial.coeff_sub, Polynomial.coeff_X_pow]
  have htrδ : Algebra.trace ↥k ↥(quadExt k δ) δ' = 0 := by
    have h := trace_adjoinSimpleGen hint
    rw [hnext, neg_zero] at h
    exact h
  -- The basis `{1, δ'}` of `k(δ)/k` (`δ ∉ k` gives independence; `hdeg` gives the right count).
  have hli : LinearIndependent ↥k ![(1 : ↥(quadExt k δ)), δ'] := by
    rw [linearIndependent_fin2]
    refine ⟨fun h0 => hδbot ?_, fun a ha => hδbot ?_⟩
    · rw [← hcoe, show (δ' : ℚ̄₂) = ((0 : ↥(quadExt k δ)) : ℚ̄₂) from congrArg _ h0]; simp
    · have haval : (algebraMap ↥k ℚ̄₂ a) * δ = 1 := by
        have := congrArg (Subtype.val) ha
        simpa [Algebra.smul_def, hcoe] using this
      rw [IntermediateField.mem_bot]
      exact ⟨a⁻¹, by rw [map_inv₀]; exact inv_eq_of_mul_eq_one_right haval⟩
  set b : Module.Basis (Fin 2) ↥k ↥(quadExt k δ) :=
    basisOfLinearIndependentOfCardEqFinrank hli (by rw [Fintype.card_fin, hdeg]) with hbdef
  have hb0 : b 0 = 1 := by simp [hbdef, coe_basisOfLinearIndependentOfCardEqFinrank]
  have hb1 : b 1 = δ' := by simp [hbdef, coe_basisOfLinearIndependentOfCardEqFinrank]
  -- On this orthogonal basis the trace form reads as the diagonal form `⟨2, 2d⟩`.
  have hbr : (traceFormOne k δ).basisRepr b = diagForm k (twoUnit k) (twoUnit k * d) := by
    ext w
    rw [QuadraticMap.basisRepr_apply, Fin.sum_univ_two, hb0, hb1, traceFormOne_apply,
      diagForm_apply]
    have hzz : (w 0 • (1 : ↥(quadExt k δ)) + w 1 • δ') * (w 0 • 1 + w 1 • δ')
        = algebraMap ↥k ↥(quadExt k δ) (w 0 * w 0 + w 1 * w 1 * (d : ↥k))
          + (w 0 * w 1 + w 0 * w 1) • δ' := by
      simp only [Algebra.smul_def, map_add, map_mul, mul_one]
      linear_combination (algebraMap ↥k ↥(quadExt k δ) (w 1)
        * algebraMap ↥k ↥(quadExt k δ) (w 1)) * hδ'sq
    rw [hzz, map_add, LinearMap.map_smul, Algebra.trace_algebraMap, htrδ, hdeg,
      show ((twoUnit k : (↥k)ˣ) : ↥k) = 2 from rfl,
      show ((twoUnit k * d : (↥k)ˣ) : ↥k) = 2 * (d : ↥k) from rfl]
    simp only [smul_zero, add_zero, nsmul_eq_mul, Nat.cast_ofNat]
    ring_nf
  exact ⟨hbr ▸ QuadraticMap.isometryEquivBasisRepr (traceFormOne k δ) b⟩

/-- **Lemma 6.16, second diagonalization**: for `a = u + vδ` with norm `n = u² − dv²`
(`u, n, d` units of `k`), `Tr⟨a⟩ ≃ ⟨2u, 2dn/u⟩` — Gram `(2u, 2vd; 2vd, 2ud)` on `{1, δ}`,
completed to squares using `u ∈ kˣ`. -/
theorem traceFormTwisted_isDiagonalization (u n d : (↥k)ˣ) (v : ↥k)
    (hn : (n : ↥k) = (u : ↥k) ^ 2 - (d : ↥k) * v ^ 2) {δ : ℚ̄₂}
    (hδ : δ ^ 2 = ((d : ↥k) : ℚ̄₂)) (hdeg : Module.finrank ↥k ↥(quadExt k δ) = 2)
    (a : ↥(quadExt k δ)) (ha : (a : ℚ̄₂) = ((u : ↥k) : ℚ̄₂) + (v : ℚ̄₂) * δ) :
    IsDiagonalization k (traceFormTwisted k δ a) (twoUnit k * u) (twoUnit k * d * n * u⁻¹) := by
  have hint : IsIntegral ↥k δ := isIntegral_of_sq_eq k d hδ
  set δ' : ↥(quadExt k δ) := IntermediateField.AdjoinSimple.gen ↥k δ with hδ'def
  have hcoe : (δ' : ℚ̄₂) = δ := IntermediateField.AdjoinSimple.coe_gen ↥k δ
  have hδbot : δ ∉ (⊥ : IntermediateField ↥k ℚ̄₂) := fun hmem => by
    have : Module.finrank ↥k ↥(quadExt k δ) = 1 :=
      IntermediateField.finrank_adjoin_simple_eq_one_iff.mpr hmem
    omega
  have hδ'sq : δ' * δ' = algebraMap ↥k ↥(quadExt k δ) (d : ↥k) := by
    apply Subtype.ext
    rw [IntermediateField.coe_algebraMap_apply]
    push_cast [hcoe]
    rw [← pow_two]; exact hδ
  have hnext : (minpoly ↥k δ).nextCoeff = 0 := by
    have hdvd : minpoly ↥k δ ∣ Polynomial.X ^ 2 - Polynomial.C (d : ↥k) :=
      minpoly.dvd ↥k δ (by simp [hδ])
    have hmonic_q : (Polynomial.X ^ 2 - Polynomial.C (d : ↥k)).Monic :=
      Polynomial.monic_X_pow_sub_C _ two_ne_zero
    have hdeg_m : (minpoly ↥k δ).natDegree = 2 :=
      (IntermediateField.adjoin.finrank hint).symm.trans hdeg
    have hmp : minpoly ↥k δ = Polynomial.X ^ 2 - Polynomial.C (d : ↥k) :=
      (Polynomial.eq_of_monic_of_dvd_of_natDegree_le (minpoly.monic hint) hmonic_q hdvd
        (by rw [Polynomial.natDegree_X_pow_sub_C]; omega)).symm
    rw [hmp, Polynomial.nextCoeff]
    simp [Polynomial.coeff_sub, Polynomial.coeff_X_pow]
  have htrδ : Algebra.trace ↥k ↥(quadExt k δ) δ' = 0 := by
    have h := trace_adjoinSimpleGen hint
    rw [hnext, neg_zero] at h
    exact h
  have hu0 : (u : ↥k) ≠ 0 := u.ne_zero
  -- `a = u + vδ` inside `k(δ)`.
  have ha' : a = algebraMap ↥k ↥(quadExt k δ) (u : ↥k) + v • δ' := by
    apply Subtype.ext
    rw [ha, AddMemClass.coe_add, Algebra.smul_def, MulMemClass.coe_mul, hcoe]
    rfl
  -- General twisted-trace value on `z = p·1 + q·δ` (uses `Tr 1 = 2`, `Tr δ = 0`, `δ² = d`).
  have htw : ∀ p q : ↥k, Algebra.trace ↥k ↥(quadExt k δ)
        (a * (algebraMap ↥k ↥(quadExt k δ) p + q • δ')
          * (algebraMap ↥k ↥(quadExt k δ) p + q • δ'))
      = 2 * ((u : ↥k) * (p ^ 2 + q ^ 2 * (d : ↥k)) + 2 * v * (p * q) * (d : ↥k)) := by
    intro p q
    have hdec : a * (algebraMap ↥k ↥(quadExt k δ) p + q • δ')
          * (algebraMap ↥k ↥(quadExt k δ) p + q • δ')
        = algebraMap ↥k ↥(quadExt k δ) ((u : ↥k) * (p ^ 2 + q ^ 2 * (d : ↥k))
            + 2 * v * (p * q) * (d : ↥k))
          + (2 * (u : ↥k) * (p * q) + v * (p ^ 2 + q ^ 2 * (d : ↥k))) • δ' := by
      rw [ha']
      simp only [Algebra.smul_def, map_add, map_mul, map_pow, map_ofNat]
      linear_combination (algebraMap ↥k ↥(quadExt k δ) (u : ↥k)
          * algebraMap ↥k ↥(quadExt k δ) q * algebraMap ↥k ↥(quadExt k δ) q
        + 2 * algebraMap ↥k ↥(quadExt k δ) v * algebraMap ↥k ↥(quadExt k δ) p
          * algebraMap ↥k ↥(quadExt k δ) q
        + algebraMap ↥k ↥(quadExt k δ) v * algebraMap ↥k ↥(quadExt k δ) q
          * algebraMap ↥k ↥(quadExt k δ) q * δ') * hδ'sq
    rw [hdec, map_add, LinearMap.map_smul, Algebra.trace_algebraMap, htrδ, hdeg]
    simp only [smul_zero, add_zero, nsmul_eq_mul, Nat.cast_ofNat]
  -- `δ` is not a scalar (it generates the quadratic extension).
  have hδ'lin : ∀ s : ↥k, δ' ≠ algebraMap ↥k ↥(quadExt k δ) s := fun s hs =>
    hδbot (IntermediateField.mem_bot.mpr
      ⟨s, by rw [← hcoe, hs, IntermediateField.coe_algebraMap_apply]⟩)
  -- Completed-square basis `{1, δ − (vd/u)·1}`.
  set c : ↥k := v * (d : ↥k) * (u : ↥k)⁻¹ with hcdef
  have hli : LinearIndependent ↥k ![(1 : ↥(quadExt k δ)), δ' - c • 1] := by
    rw [linearIndependent_fin2]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    refine ⟨fun h0 => hδ'lin c ((sub_eq_zero.mp h0).trans (by rw [Algebra.smul_def, mul_one])),
      fun s hs => ?_⟩
    rcases eq_or_ne s 0 with rfl | hs0
    · rw [zero_smul] at hs; exact one_ne_zero hs.symm
    · refine hδ'lin (s⁻¹ + c) ?_
      have h1 : δ' - c • (1 : ↥(quadExt k δ)) = s⁻¹ • (1 : ↥(quadExt k δ)) := by
        have h := congrArg (fun t => s⁻¹ • t) hs
        simpa only [smul_smul, inv_mul_cancel₀ hs0, one_smul] using h
      rw [sub_eq_iff_eq_add.mp h1, ← add_smul, Algebra.smul_def, mul_one]
  set e : Module.Basis (Fin 2) ↥k ↥(quadExt k δ) :=
    basisOfLinearIndependentOfCardEqFinrank hli (by rw [Fintype.card_fin, hdeg]) with hedef
  have he0 : e 0 = 1 := by simp [hedef, coe_basisOfLinearIndependentOfCardEqFinrank]
  have he1 : e 1 = δ' - c • 1 := by simp [hedef, coe_basisOfLinearIndependentOfCardEqFinrank]
  have hval2 : ((twoUnit k : (↥k)ˣ) : ↥k) = 2 := rfl
  have hbr : (traceFormTwisted k δ a).basisRepr e
      = diagForm k (twoUnit k * u) (twoUnit k * d * n * u⁻¹) := by
    ext w
    rw [QuadraticMap.basisRepr_apply, Fin.sum_univ_two, he0, he1, traceFormTwisted_apply,
      diagForm_apply]
    have hz : (w 0 • (1 : ↥(quadExt k δ)) + w 1 • (δ' - c • 1))
        = algebraMap ↥k ↥(quadExt k δ) (w 0 - w 1 * c) + w 1 • δ' := by
      simp only [Algebra.smul_def, map_sub, map_mul, mul_one]; ring
    rw [hz, htw (w 0 - w 1 * c) (w 1),
      show ((twoUnit k * u : (↥k)ˣ) : ↥k) = 2 * (u : ↥k) by rw [Units.val_mul, hval2],
      show ((twoUnit k * d * n * u⁻¹ : (↥k)ˣ) : ↥k) = 2 * (d : ↥k) * (n : ↥k) * (u : ↥k)⁻¹ by
        simp only [Units.val_mul, Units.val_inv_eq_inv_val, hval2],
      hcdef, hn]
    field_simp
    ring_nf
  exact ⟨hbr ▸ QuadraticMap.isometryEquivBasisRepr (traceFormTwisted k δ a) e⟩

end TraceForms

/-! ## Draft axiom statement (for owner review; will move to Foundations/Axioms.lean at T5)

The B9-A replacement axiom, stated as a sorried `theorem` so that it elaborates and can be
reviewed as a compiling artifact (plan risk R3).  **It is never proved on this branch**: after
owner sign-off, ticket T5 moves the statement verbatim to `GQ2/Foundations/Axioms.lean` as an
`axiom` (census label B9) and derives today's `evensKahn_dyadic` from it, byte-identically. -/

/-- **Draft — the B9-A axiom `relativeStiefelWhitney_dyadic`** (Kahn, Invent. Math. 78 (1984),
Théorème 2 at the rank-1 form `⟨a⟩`, expanded through Evens Thm 1 / Kozlowski Thm 1.1 at
index 2; paper eq. (111), degrees ≤ 2), over an arbitrary finite dyadic base `k`.

Setting, as in B9: `k/ℚ₂` finite inside the fixed `ℚ̄₂`; `d ∈ kˣ` with `δ² = d`;
`L = k(δ) = quadExt k δ`, quadratic over `k` (`hdeg`, provable from `hidx`/`hUo` via
`finrank_quadExt_eq_two` but carried so the statement is locally Kahn's `L/k` setting);
`G_L ∩ G_k` is the stabilizer subgroup of `δ` (the verbatim B9 encoding: `hidx`, `s`, `hs`,
`htriv`, `hUo`); `a ∈ Lˣ` **arbitrary** (the new generality — B9's `a = u + vδ` disappears),
entering degree-wise through the Kummer 1-cocycle `α` of a square root `β` of `a`
(`hβ`/`hβ0`/`hαdef`/`hα`/`hαc`, verbatim B9 plumbing).  With `w₁ = swOne k`,
`w₂ = swTwo k htriv` the Stiefel–Whitney classes of `GQ2/StiefelWhitney.lean`, the two
components of Kahn's identity `w(Tr⟨a⟩) = w(Tr⟨1⟩)·(1 + cor[a] + N^{Ev}[a])` read:

* degree 1: `w₁(Tr⟨a⟩) = w₁(Tr⟨1⟩) + cor[a]`;
* degree 2: `w₂(Tr⟨a⟩) = w₂(Tr⟨1⟩) + w₁(Tr⟨1⟩) ⌣ cor[a] + N^{Ev}[a]`.

Deviations (flagged, unchanged from B9): truncation to degrees ≤ 2; `N^{Ev}` *defined* by the
two-point graph cocycle (98) (`evensNormH2`, Lemma 6.13); finite dyadic base.  Removed
relative to B9: the Lemma 6.16 diagonalization scoping — the left-hand sides are now genuine
isometry-class invariants. -/
theorem relativeStiefelWhitney_dyadic
    (k : IntermediateField ℚ_[2] (AlgebraicClosure ℚ_[2])) [FiniteDimensional ℚ_[2] k]
    (d : (↥k)ˣ)
    (δ β : AlgebraicClosure ℚ_[2])
    (hδ : δ ^ 2 = ((d : ↥k) : AlgebraicClosure ℚ_[2]))
    (hdeg : Module.finrank ↥k ↥(quadExt k δ) = 2)
    (a : (↥(quadExt k δ))ˣ)
    (hβ : β ^ 2 = ((a : ↥(quadExt k δ)) : AlgebraicClosure ℚ_[2]))
    (hβ0 : β ≠ 0)
    (hidx : ((MulAction.stabilizer (Kummer.GaloisGroup ℚ_[2]) δ).subgroupOf
        k.fixingSubgroup).index = 2)
    (s : k.fixingSubgroup)
    (hs : s ∉ (MulAction.stabilizer (Kummer.GaloisGroup ℚ_[2]) δ).subgroupOf k.fixingSubgroup)
    (htriv : ∀ (g : k.fixingSubgroup) (m : ZMod 2), g • m = m)
    (hUo : IsOpen (((MulAction.stabilizer (Kummer.GaloisGroup ℚ_[2]) δ).subgroupOf
        k.fixingSubgroup : Subgroup k.fixingSubgroup) : Set k.fixingSubgroup))
    (α : ((MulAction.stabilizer (Kummer.GaloisGroup ℚ_[2]) δ).subgroupOf
        k.fixingSubgroup) → ZMod 2)
    (hαdef : ∀ g, α g = Kummer.kummerCocycleFun β
        ((g : k.fixingSubgroup) : Kummer.GaloisGroup ℚ_[2]))
    (hα : ∀ g h, α (g * h) = α g + α h)
    (hαc : Continuous α) :
    (swOne k (traceFormTwisted k δ ↑a)
      = swOne k (traceFormOne k δ) + corH1 htriv hUo hidx hs α hα hαc)
    ∧ (swTwo k htriv (traceFormTwisted k δ ↑a)
      = swTwo k htriv (traceFormOne k δ)
        + swOne k (traceFormOne k δ) ⌣[htriv] corH1 htriv hUo hidx hs α hα hαc
        + evensNormH2 htriv hUo hidx hs α hα hαc) :=
  sorry -- T5: becomes the B9-A axiom in Foundations/Axioms.lean after owner sign-off

end GQ2
