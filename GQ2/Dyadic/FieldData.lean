/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Opus-5
-/
import GQ2.Dyadic.Certificates.L
import GQ2.Dyadic.LocalGauss.EulerShapiro
import GQ2.Dyadic.LocalGauss.Q0

/-!
# Dyadic campaign, ticket FD1: the field-side data of `H¹(G_K, 𝔽₂)`

Scaffolding probe (§1 draft).
-/

namespace GQ2.Dyadic.FieldData

open ContCoh GQ2

local notation "ℚ̄₂" => AlgebraicClosure ℚ_[2]

variable (K : IntermediateField ℚ_[2] ℚ̄₂) [FiniteDimensional ℚ_[2] K]

section Probes

example : IsGalois ℚ_[2] ℚ̄₂ := inferInstance
example : Module.finrank ℚ_[2] K = K.fixingSubgroup.index :=
  IntermediateField.finrank_eq_fixingSubgroup_index K

end Probes

/-! ## §1 The dimension of `H¹(G_K, 𝔽₂)` -/

section Dimension

/-- `G_K` has finite index in `G_ℚ₂` (open subgroup of a profinite group). -/
theorem finiteIndex_fixingSubgroup :
    (K.fixingSubgroup : Subgroup AbsGalQ2).FiniteIndex :=
  @Subgroup.finiteIndex_of_finite_quotient _ _ _
    (finite_quotient_of_isOpen _ (isOpen_fixingSubgroup K))

/-- `G_K = Gal(ℚ̄₂/K)` is a local dualizing group: it is an open finite-index subgroup of
`G_ℚ₂`, which is exactly the gate on the base-generalized B6 axiom `GQ2.tateDualityAt`. -/
theorem galK_isLocalDualizingGroup (n : ℕ) [NeZero n] :
    IsLocalDualizingGroup ↥(K.fixingSubgroup) n :=
  @subgroup_isLocalDualizingGroup n _ _ (isOpen_fixingSubgroup K)
    (finiteIndex_fixingSubgroup K)

/-- **The B6 duality bundle at `G_K`**, for `K/ℚ₂` finite. -/
noncomputable def tateDualityGalK : TateDualityG ↥(K.fixingSubgroup) 2 :=
  tateDualityAt ↥(K.fixingSubgroup) 2 (galK_isLocalDualizingGroup K 2)

/-- `G_K` acts trivially on `μ₂ ⊂ ℚ₂`. -/
theorem smul_muN_two_galK (g : ↥(K.fixingSubgroup)) (x : MuN 2) : g • x = x :=
  LocalLiftingDuality.smul_muN_two_trivial g.1 x

/-- The coefficient transport `𝔽₂ ≃+ μ₂` is `G_K`-equivariant (both actions are trivial). -/
theorem muNTwoEquiv_symm_equivariant (g : ↥(K.fixingSubgroup)) (a : ZMod 2) :
    LocalLiftingDuality.muNTwoEquiv.symm (g • a)
      = g • LocalLiftingDuality.muNTwoEquiv.symm a := by
  rw [smul_muN_two_galK K, show g • a = a from rfl]

/-- **The invariant map at `G_K` in `𝔽₂`-coefficients**: `H²(G_K, 𝔽₂) ≃+ 𝔽₂`, obtained from
B6's `inv : H²(G_K, μ₂) ≃+ ℤ/2` by the (trivial-action) transport `𝔽₂ ≃+ μ₂`.  For `n = 2` the
"unnormalized" deviation flagged on B6 is vacuous: `ZMod 2` has a unique automorphism. -/
noncomputable def invGalK : H2 ↥(K.fixingSubgroup) (ZMod 2) ≃+ ZMod 2 :=
  (H2congr LocalLiftingDuality.muNTwoEquiv.symm (muNTwoEquiv_symm_equivariant K)).trans
    (tateDualityGalK K).inv

omit [FiniteDimensional ℚ_[2] K] in
/-- `H⁰(G_K, 𝔽₂) = 𝔽₂`: the coefficient action is trivial, so the invariants are everything. -/
theorem h0_zmodTwo_eq_top : H0 ↥(K.fixingSubgroup) (ZMod 2) = ⊤ :=
  eq_top_iff.mpr fun _ _ _ => rfl

omit [FiniteDimensional ℚ_[2] K] in
/-- `#H⁰(G_K, 𝔽₂) = 2`. -/
theorem card_H0_zmodTwo : Nat.card ↥(H0 ↥(K.fixingSubgroup) (ZMod 2)) = 2 := by
  rw [h0_zmodTwo_eq_top, Nat.card_congr (AddSubgroup.topEquiv (G := ZMod 2)).toEquiv]
  simp

/-- **`#H²(G_K, 𝔽₂) = 2`** — the `dim H² = 1` clause, from B6's invariant map. -/
theorem card_H2_zmodTwo : Nat.card (H2 ↥(K.fixingSubgroup) (ZMod 2)) = 2 := by
  rw [Nat.card_congr (invGalK K).toEquiv]
  simp

/-- `H¹(G_K, 𝔽₂)` is finite (B7 at `K`). -/
theorem finite_H1_zmodTwo : Finite (H1 ↥(K.fixingSubgroup) (ZMod 2)) :=
  (absGalK_localEulerCharacteristic K (ZMod 2)).2.1

/-- **Fact (i): `#H¹(G_K, 𝔽₂) = 2 ^ (n + 2)`**, `n = [K : ℚ₂]`.

The local Euler–Poincaré characteristic at `K` (B7 through `absGalK_localEulerCharacteristic`)
reads `#H¹ = #H⁰ · #H² · 2^(n · v₂(#V))`; at the trivial module `V = 𝔽₂` the two outer factors
are `2` (`card_H0_zmodTwo`, `card_H2_zmodTwo` — the latter is B6) and `v₂(2) = 1`.  This is
MC1 §(ix)'s `card_H1 = 2^{n+2}` convention, at the field. -/
theorem card_H1_zmodTwo :
    Nat.card (H1 ↥(K.fixingSubgroup) (ZMod 2)) = 2 ^ (Module.finrank ℚ_[2] K + 2) := by
  have h := (absGalK_localEulerCharacteristic K (ZMod 2)).2.2.2
  rw [card_H0_zmodTwo, card_H2_zmodTwo, Nat.card_zmod,
    show padicValNat 2 2 = 1 from padicValNat.self one_lt_two, mul_one,
    ← IntermediateField.finrank_eq_fixingSubgroup_index K] at h
  rw [h, pow_add]
  ring

end Dimension

/-! ## §1.1 The dimension, as a dimension

`H¹(G_K,𝔽₂)` is elementary abelian, so it is an `𝔽₂`-vector space; `card_H1_zmodTwo` then reads
as `dim_{𝔽₂} H¹(G_K,𝔽₂) = n + 2`, in both of the repo's dimension vocabularies
(`Module.finrank` and `demushkinRank`). -/

section Finrank

variable {Γ : Type*} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
  [DistribMulAction Γ (ZMod 2)] [ContinuousSMul Γ (ZMod 2)]

/-- `H¹(Γ, 𝔽₂)` is a `ZMod 2`-module (exponent `2`, being a subquotient of `𝔽₂`-cochains).  The
`H²` twin is `GQ2.RStage.instModuleH2`; the `H¹` one did not exist. -/
instance instModuleH1 : Module (ZMod 2) (H1 Γ (ZMod 2)) :=
  AddCommGroup.zmodModule (fun x => nsmul_H1_eq_zero x)

end Finrank

section FinrankK

/-- **Fact (i), in `Module.finrank` form**: `dim_{𝔽₂} H¹(G_K, 𝔽₂) = n + 2`. -/
theorem finrank_H1_zmodTwo :
    Module.finrank (ZMod 2) (H1 ↥(K.fixingSubgroup) (ZMod 2)) = Module.finrank ℚ_[2] K + 2 := by
  haveI := finite_H1_zmodTwo K
  have h : (2 : ℕ) ^ Module.finrank (ZMod 2) (H1 ↥(K.fixingSubgroup) (ZMod 2))
      = 2 ^ (Module.finrank ℚ_[2] K + 2) := by
    rw [FiniteField.pow_finrank_eq_natCard 2 (H1 ↥(K.fixingSubgroup) (ZMod 2)),
      card_H1_zmodTwo K]
  exact Nat.pow_right_injective le_rfl h

/-- **Fact (i), in `demushkinRank` form** — the vocabulary MC1 §(ix) and the `MarkedCore`
consumers use (`coreRank h = 4 + 2h` is `n + 2` at `n = 2 + 2h`). -/
theorem demushkinRank_galK :
    demushkinRank 2 ↥(K.fixingSubgroup) = Module.finrank ℚ_[2] K + 2 :=
  demushkinRank_eq_of_card (card_H1_zmodTwo K)

end FinrankK

end GQ2.Dyadic.FieldData
