/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Opus-4.8 and Fable-5
-/
module

public import GQ2.CupProduct

@[expose] public section

/-!
# Cup graded-commutativity in characteristic 2

The `(1,1)` cup product is graded-commutative: `c ∪_μ d = (-1)^{1·1} d ∪_{μᵀ} c`, where `μᵀ` is
the transposed pairing.  In characteristic 2 the sign disappears, giving

  `cup11 μ c d = cup11 μ.flip d c`   (for a 2-torsion target `P`).

The proof is a clean cochain homotopy that holds **over `ℤ`** at the cocycle level:
`cup11Fun μ a b + cup11Fun μᵀ b a = δ¹(g ↦ −μ(a g)(b g))` (`cup11Fun_add_flip_eq_dOne`);
2-torsion of `P` is used only to turn the class difference `α − β` into the sum `α + β`.

This is the general form of `GQ2.HilbertLedger.trivialCupPairing_comm` (the Hilbert-ledger proof), which is the
special case `μ = AddMonoidHom.mul` on the trivial `𝔽₂`-module (`μ.flip = μ` by `mul_comm`); a
future refactor can derive that lemma from `cup11_comm` here.  Designed to live in
`GQ2/CupProduct.lean` (kept in a separate file for now to avoid churn on the shared foundation).
-/

namespace GQ2.ContCoh

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable {M : Type*} [AddCommGroup M] [TopologicalSpace M] [IsTopologicalAddGroup M]
  [DiscreteTopology M] [DistribMulAction G M] [ContinuousSMul G M]
variable {N : Type*} [AddCommGroup N] [TopologicalSpace N] [IsTopologicalAddGroup N]
  [DiscreteTopology N] [DistribMulAction G N] [ContinuousSMul G N]
variable {P : Type*} [AddCommGroup P] [TopologicalSpace P] [IsTopologicalAddGroup P]
  [DiscreteTopology P] [DistribMulAction G P] [ContinuousSMul G P]
variable (μ : M →+ N →+ P)
  (hμ : ∀ (g : G) (m : M) (n : N), μ (g • m) (g • n) = g • μ m n)

omit [TopologicalSpace G] [IsTopologicalGroup G] [TopologicalSpace M] [IsTopologicalAddGroup M]
  [DiscreteTopology M] [ContinuousSMul G M] [TopologicalSpace N] [IsTopologicalAddGroup N]
  [DiscreteTopology N] [ContinuousSMul G N] [TopologicalSpace P] [IsTopologicalAddGroup P]
  [DiscreteTopology P] [ContinuousSMul G P] in
include hμ in
/-- The transposed pairing `μᵀ = μ.flip` is `G`-equivariant when `μ` is. -/
lemma flip_equivariant :
    ∀ (g : G) (n : N) (m : M), μ.flip (g • n) (g • m) = g • μ.flip n m :=
  fun g n m => by simpa only [AddMonoidHom.flip_apply] using hμ g m n

omit [IsTopologicalGroup G] [DiscreteTopology M] [ContinuousSMul G M] [DiscreteTopology N]
  [ContinuousSMul G N] [TopologicalSpace P] [IsTopologicalAddGroup P] [DiscreteTopology P]
  [ContinuousSMul G P] in
include hμ in
/-- **The graded-commutativity homotopy** (valid over `ℤ`): for cocycles `a, b`,
`(a ∪_μ b) + (b ∪_{μᵀ} a) = δ¹(g ↦ −μ(a g)(b g))`.  Expanding `δ¹` with the cocycle identities
for `a, b` and the equivariance `hμ` leaves exactly `a ∪_μ b + b ∪_{μᵀ} a`. -/
lemma cup11Fun_add_flip_eq_dOne (a : Z1 G M) (b : Z1 G N) :
    cup11Fun μ a.1 b.1 + cup11Fun μ.flip b.1 a.1
      = dOne G P (fun g => -μ (a.1 g) (b.1 g)) := by
  ext ⟨g, h⟩
  simp only [cup11Fun, AddMonoidHom.flip_apply, Pi.add_apply, dOne, AddMonoidHom.coe_mk,
    ZeroHom.coe_mk]
  rw [(mem_Z1_iff.mp a.2).2 g h, (mem_Z1_iff.mp b.2).2 g h]
  simp only [map_add, AddMonoidHom.add_apply, smul_neg, ← hμ]
  abel

omit [IsTopologicalGroup G] [DiscreteTopology P] [ContinuousSMul G P] in
include hμ in
/-- **Cup graded-commutativity in characteristic 2**: for a `2`-torsion target `P`,
`cup11 μ c d = cup11 μ.flip d c` in `H²`. -/
theorem cup11_comm (hP2 : ∀ p : P, p + p = 0) (x : H1 G M) (y : H1 G N) :
    cup11 μ hμ x y = cup11 μ.flip (flip_equivariant μ hμ) y x := by
  obtain ⟨a, rfl⟩ := H1mk_surjective (G := G) (M := M) x
  obtain ⟨b, rfl⟩ := H1mk_surjective (G := G) (M := N) y
  rw [cup11_mk_mk, cup11_mk_mk, ← sub_eq_zero, ← map_sub, ← AddMonoidHom.mem_ker]
  change _ ∈ (QuotientAddGroup.mk' _).ker
  rw [QuotientAddGroup.ker_mk', AddSubgroup.mem_addSubgroupOf]
  show cup11Fun μ a.1 b.1 - cup11Fun μ.flip b.1 a.1 ∈ B2 G P
  rw [sub_eq_add_neg, show -cup11Fun μ.flip b.1 a.1 = cup11Fun μ.flip b.1 a.1 from
      funext fun p => neg_eq_of_add_eq_zero_left (hP2 _),
    cup11Fun_add_flip_eq_dOne μ hμ a b]
  exact AddSubgroup.mem_map.mpr ⟨_,
    (continuous_pairing μ (mem_Z1_iff.mp a.2).1 (mem_Z1_iff.mp b.2).1).neg, rfl⟩

omit [IsTopologicalAddGroup M] [ContinuousSMul G N] [DiscreteTopology P] [ContinuousSMul G P] in
include hμ in
/-- **Graded-commutativity for the `(0,2)`/`(2,0)` pair** (no characteristic hypothesis needed):
`cup02 μ c d = cup20 μᵀ d c`.  The `(g·h)`-twist in `cup20` is absorbed because the `H⁰` element
`c` is invariant, so the two cup cochains are *equal* — no homotopy. -/
theorem cup02_eq_cup20_flip (c : ↥(H0 G M)) (d : H2 G N) :
    cup02 μ hμ c d = cup20 μ.flip (flip_equivariant μ hμ) d c := by
  obtain ⟨b, rfl⟩ := H2mk_surjective (G := G) (M := N) d
  show H2mk G P ⟨cup02Fun μ c.1 b.1, cup02_mem_Z2 μ hμ c b⟩
      = H2mk G P ⟨cup20Fun μ.flip b.1 c.1, cup20_mem_Z2 μ.flip (flip_equivariant μ hμ) b c⟩
  congr 1
  refine Subtype.ext (funext fun p => ?_)
  show μ c.1 (b.1 p) = μ.flip (b.1 p) ((p.1 * p.2) • c.1)
  rw [AddMonoidHom.flip_apply, c.2]

omit [ContinuousSMul G M] [IsTopologicalAddGroup N] [DiscreteTopology P] [ContinuousSMul G P] in
include hμ in
/-- **Graded-commutativity for the `(2,0)`/`(0,2)` pair** (the transpose of `cup02_eq_cup20_flip`):
`cup20 μ c d = cup02 μᵀ d c`.  Again the `(g·h)`-twist is absorbed by invariance of the `H⁰`
element `d`, so the cochains are equal on the nose. -/
theorem cup20_eq_cup02_flip (c : H2 G M) (d : ↥(H0 G N)) :
    cup20 μ hμ c d = cup02 μ.flip (flip_equivariant μ hμ) d c := by
  obtain ⟨b, rfl⟩ := H2mk_surjective (G := G) (M := M) c
  show H2mk G P ⟨cup20Fun μ b.1 d.1, cup20_mem_Z2 μ hμ b d⟩
      = H2mk G P ⟨cup02Fun μ.flip d.1 b.1, cup02_mem_Z2 μ.flip (flip_equivariant μ hμ) d b⟩
  congr 1
  refine Subtype.ext (funext fun p => ?_)
  show μ (b.1 p) ((p.1 * p.2) • d.1) = μ.flip d.1 (b.1 p)
  rw [AddMonoidHom.flip_apply, d.2]

omit [IsTopologicalGroup G] [IsTopologicalAddGroup M] [ContinuousSMul G M] [ContinuousSMul G N]
  [DiscreteTopology P] [ContinuousSMul G P] in
include hμ in
/-- Class formula for the `(0,2)` cup (definitional, like `cup11_mk_mk`). -/
@[simp] lemma cup02_mk_mk (m : ↥(H0 G M)) (b : Z2 G N) :
    cup02 μ hμ m (H2mk G N b) = H2mk G P ⟨cup02Fun μ m.1 b.1, cup02_mem_Z2 μ hμ m b⟩ := rfl

omit [ContinuousSMul G M] [IsTopologicalAddGroup N] [DiscreteTopology P] [ContinuousSMul G P] in
include hμ in
/-- Class formula for the `(2,0)` cup (definitional, like `cup11_mk_mk`). -/
@[simp] lemma cup20_mk_mk (a : Z2 G M) (n : ↥(H0 G N)) :
    cup20 μ hμ (H2mk G M a) n = H2mk G P ⟨cup20Fun μ a.1 n.1, cup20_mem_Z2 μ hμ a n⟩ := rfl

/-! ## Cohomology transport along a `G`-equivariant module isomorphism

The repo's `mapCoeff1`/`mapCoeff2` have no functoriality lemmas; these package a `G`-equivariant
`AddEquiv` of coefficients into `AddEquiv`s on `H¹`/`H²`, which the duality transport needs. -/

section Transport

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable {M : Type*} [AddCommGroup M] [TopologicalSpace M] [IsTopologicalAddGroup M]
  [DiscreteTopology M] [DistribMulAction G M] [ContinuousSMul G M]
variable {N : Type*} [AddCommGroup N] [TopologicalSpace N] [IsTopologicalAddGroup N]
  [DiscreteTopology N] [DistribMulAction G N] [ContinuousSMul G N]
variable (e : M ≃+ N) (he : ∀ (g : G) (m : M), e (g • m) = g • e m)

omit [TopologicalSpace G] [IsTopologicalGroup G] [TopologicalSpace M] [IsTopologicalAddGroup M]
  [DiscreteTopology M] [ContinuousSMul G M] [TopologicalSpace N] [IsTopologicalAddGroup N]
  [DiscreteTopology N] [ContinuousSMul G N] in
include he in
/-- The inverse of a `G`-equivariant coefficient equivalence is `G`-equivariant. -/
lemma addEquiv_symm_equivariant : ∀ (g : G) (n : N), e.symm (g • n) = g • e.symm n :=
  fun g n => by apply e.injective; rw [e.apply_symm_apply, he, e.apply_symm_apply]

/-- **`H¹` transport**: a `G`-equivariant `AddEquiv` of coefficients induces one on `H¹`. -/
noncomputable def H1congr : H1 G M ≃+ H1 G N where
  toFun := mapCoeff1 e.toAddMonoidHom continuous_of_discreteTopology he
  invFun := mapCoeff1 e.symm.toAddMonoidHom continuous_of_discreteTopology
    (addEquiv_symm_equivariant e he)
  left_inv x := by
    induction x using QuotientAddGroup.induction_on with
    | H a =>
      rw [show (QuotientAddGroup.mk a : H1 G M) = H1mk G M a from rfl, mapCoeff1_H1mk,
        mapCoeff1_H1mk]
      exact congrArg (H1mk G M) (Subtype.ext (funext fun g => e.symm_apply_apply _))
  right_inv x := by
    induction x using QuotientAddGroup.induction_on with
    | H a =>
      rw [show (QuotientAddGroup.mk a : H1 G N) = H1mk G N a from rfl, mapCoeff1_H1mk,
        mapCoeff1_H1mk]
      exact congrArg (H1mk G N) (Subtype.ext (funext fun g => e.apply_symm_apply _))
  map_add' := map_add _

omit [IsTopologicalGroup G] [ContinuousSMul G M] [ContinuousSMul G N] in
include he in
/-- `H1congr` on a class is post-composition of a cocycle representative (definitional). -/
lemma H1congr_mk (a : Z1 G M) :
    H1congr e he (H1mk G M a)
      = H1mk G N (Z1comap (ContinuousMonoidHom.id G) e.toAddMonoidHom
          continuous_of_discreteTopology he a) := rfl

omit [IsTopologicalGroup G] [ContinuousSMul G M] [DiscreteTopology N] [ContinuousSMul G N] in
include he in
/-- `mapCoeff2` on a class: post-composition of a 2-cocycle representative. -/
lemma mapCoeff2_H2mk (a : Z2 G M) :
    mapCoeff2 e.toAddMonoidHom continuous_of_discreteTopology he (H2mk G M a)
      = H2mk G N (Z2comap (ContinuousMonoidHom.id G) e.toAddMonoidHom
          continuous_of_discreteTopology he a) := rfl

/-- **`H²` transport**: a `G`-equivariant `AddEquiv` of coefficients induces one on `H²`. -/
noncomputable def H2congr : H2 G M ≃+ H2 G N where
  toFun := mapCoeff2 e.toAddMonoidHom continuous_of_discreteTopology he
  invFun := mapCoeff2 e.symm.toAddMonoidHom continuous_of_discreteTopology
    (addEquiv_symm_equivariant e he)
  left_inv x := by
    induction x using QuotientAddGroup.induction_on with
    | H a =>
      rw [show (QuotientAddGroup.mk a : H2 G M) = H2mk G M a from rfl, mapCoeff2_H2mk,
        mapCoeff2_H2mk]
      exact congrArg (H2mk G M) (Subtype.ext (funext fun p => e.symm_apply_apply _))
  right_inv x := by
    induction x using QuotientAddGroup.induction_on with
    | H a =>
      rw [show (QuotientAddGroup.mk a : H2 G N) = H2mk G N a from rfl, mapCoeff2_H2mk,
        mapCoeff2_H2mk]
      exact congrArg (H2mk G N) (Subtype.ext (funext fun p => e.apply_symm_apply _))
  map_add' := map_add _

omit [IsTopologicalGroup G] [ContinuousSMul G M] [ContinuousSMul G N] in
include he in
/-- `H2congr` on a class is post-composition of a 2-cocycle representative (definitional). -/
lemma H2congr_mk (a : Z2 G M) :
    H2congr e he (H2mk G M a)
      = H2mk G N (Z2comap (ContinuousMonoidHom.id G) e.toAddMonoidHom
          continuous_of_discreteTopology he a) := rfl

/-- **`H⁰` transport**: a `G`-equivariant `AddEquiv` of coefficients induces one on the invariants
`H⁰` (needed for the degree-`(2,0)` duality clause). -/
def H0congr : ↥(H0 G M) ≃+ ↥(H0 G N) where
  toFun := mapCoeff0 e.toAddMonoidHom he
  invFun := mapCoeff0 e.symm.toAddMonoidHom (addEquiv_symm_equivariant e he)
  left_inv x := Subtype.ext (e.symm_apply_apply x.1)
  right_inv x := Subtype.ext (e.apply_symm_apply x.1)
  map_add' := map_add _


end Transport

end GQ2.ContCoh
