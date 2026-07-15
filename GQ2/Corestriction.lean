/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Opus-4.8 and Fable-5
-/
module

public import Mathlib.Data.ZMod.Defs
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.Instances.ZMod
public import Mathlib.Tactic.Group
public import GQ2.Cohomology

@[expose] public section

/-!
# Transversal calculus: Shapiro cochains and degree-2 corestriction

The paper's §6 evaluates determinant classes through the **normalized bar corestriction** and the
**normalized Shapiro map** for an open finite-index subgroup `U ≤ G` (eqs. (97), (106), (108)):

* `ℓ_u(γ) = ũ⁻¹ · γ · (γ⁻¹·u)~ ∈ U` — the transversal 1-cochain attached to a coset `u ∈ G/U`
  (`~` = the chosen representative of a coset);
* `Sh(α)(γ)_u = α(ℓ_u(γ))` — the Shapiro cochain of `α : U → 𝔽₂` (paper's `b(γ)_h`, left-regular
  convention of Lemma 6.15's proof);
* `(cor ν)(γ, η) = Σ_u ν(ℓ_u(γ), ℓ_{γ⁻¹·u}(η))` — the degree-2 corestriction of a 2-cochain
  `ν` on `U`  (eq. (108));
* `(cor α)(γ) = Σ_u α(ℓ_u(γ))` — the degree-1 corestriction (the summed Shapiro coordinates,
  eq. (106)'s degree-1 shadow; at index 2 this is `GQ2/EvensKahn.lean`'s `corFun` up to the
  transversal choice).

**Encoding decisions** (`docs/section67-extraction.md` §D2):

* **The transversal is `Quotient.out`** (the canonical choice-function representative).  The paper
  quantifies over transversals and proves the class is independent of the choice (Lemmas 6.13/6.15,
  "up to the normalized coboundary caused by a change of transversal"); fixing the canonical one
  makes every definition here choice-parameter-free.  Transversal-independence, where needed,
  is part of the §§6–7 proof obligations.  **Deviation flagged.**
* Sums are `finsum` (`∑ᶠ`), meaningful under `[Finite (G ⧸ U)]` (finite index) — total without it.
* `H2ofFun`/`H1ofFun` are **junk-total class formers**: they send a raw function to its
  cohomology class when it is a (continuous) cocycle and to `0` otherwise.  This permits
  definitions of classes whose cocycle property is proved separately (the paper's Lemma
  6.1/6.15 content), keeping all `def`s
  total and independent of the proof layer.

Cocycle membership, Mackey restriction, and transversal-independence are proved downstream.
This file is definition-only.
-/

namespace GQ2

open ContCoh

namespace Corestriction

variable {G : Type*} [Group G]

/-! ## The transversal 1-cochain `ℓ` -/

/-- The raw transversal word `ℓ_u(γ) = ũ⁻¹ · γ · (γ⁻¹·u)~`, with `~` the canonical
representative (`Quotient.out`) and `γ⁻¹·u` the natural left action of `G` on `G ⧸ U`. -/
noncomputable def lWord (U : Subgroup G) (u : G ⧸ U) (γ : G) : G :=
  u.out⁻¹ * γ * (γ⁻¹ • u : G ⧸ U).out

/-- `ℓ_u(γ)` lands in `U`. -/
theorem lWord_mem (U : Subgroup G) (u : G ⧸ U) (γ : G) : lWord U u γ ∈ U := by
  have h2 : ((γ⁻¹ * u.out : G) : G ⧸ U) = γ⁻¹ • u := by
    conv_rhs => rw [← QuotientGroup.out_eq' u]
    exact MulAction.Quotient.smul_mk U γ⁻¹ u.out
  rw [lWord, show u.out⁻¹ * γ = (γ⁻¹ * u.out)⁻¹ by group]
  exact (QuotientGroup.eq (s := U)).mp (h2.trans (QuotientGroup.out_eq' _).symm)

/-- The transversal 1-cochain `ℓ_u(γ) ∈ U` (paper's `ℓ_u`, proof of Lemma 6.15, eq. (108)). -/
noncomputable def lTrans (U : Subgroup G) (u : G ⧸ U) (γ : G) : U := ⟨lWord U u γ, lWord_mem U u γ⟩

/-! ## Shapiro cochains and corestriction -/

/-- The **normalized Shapiro cochain** of `α : U → 𝔽₂`: `Sh(α)(γ)_u = α(ℓ_u(γ))`
(the paper's `b(γ)_h`, left-regular convention). -/
noncomputable def shapiroFun (U : Subgroup G) (α : U → ZMod 2) : G → (G ⧸ U) → ZMod 2 :=
  fun γ u ↦ α (lTrans U u γ)

/-- The **degree-1 corestriction** `(cor α)(γ) = Σ_u α(ℓ_u(γ))` (eq. (106)'s degree-1 form;
at index 2 this is `GQ2/EvensKahn.lean`'s `corFun` up to transversal choice). -/
noncomputable def cor1Fun (U : Subgroup G) (α : U → ZMod 2) : G → ZMod 2 :=
  fun γ ↦ ∑ᶠ u : G ⧸ U, α (lTrans U u γ)

/-- The **degree-2 corestriction** of a 2-cochain `ν` on `U` (paper eq. (108)):
`(cor ν)(γ, η) = Σ_u ν(ℓ_u(γ), ℓ_{γ⁻¹·u}(η))`. -/
noncomputable def cor2Fun (U : Subgroup G) (ν : U × U → ZMod 2) : G × G → ZMod 2 :=
  fun p ↦ ∑ᶠ u : G ⧸ U, ν (lTrans U u p.1, lTrans U (p.1⁻¹ • u) p.2)

end Corestriction

/-! ## Junk-total class formers

Send a raw function to its cohomology class when it is a continuous cocycle, and to `0`
otherwise.  These let statement files *define* classes whose cocycle property was, during
development, one of their own separately stated obligations, keeping the `def`s
total. -/

section ClassFormers

open scoped Classical in
/-- The `H¹`-class of a raw function, or `0` if it is not a continuous 1-cocycle. -/
noncomputable def H1ofFun (G : Type*) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [DistribMulAction G (ZMod 2)] [ContinuousSMul G (ZMod 2)] (φ : G → ZMod 2) :
    H1 G (ZMod 2) :=
  if h : φ ∈ Z1 G (ZMod 2) then H1mk G (ZMod 2) ⟨φ, h⟩ else 0

open scoped Classical in
/-- The `H²`-class of a raw function, or `0` if it is not a continuous 2-cocycle. -/
noncomputable def H2ofFun (G : Type*) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [DistribMulAction G (ZMod 2)] [ContinuousSMul G (ZMod 2)] (φ : G × G → ZMod 2) :
    H2 G (ZMod 2) :=
  if h : φ ∈ Z2 G (ZMod 2) then H2mk G (ZMod 2) ⟨φ, h⟩ else 0

/-- Evaluation rule for `H1ofFun` on an actual cocycle. -/
theorem H1ofFun_of_mem {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [DistribMulAction G (ZMod 2)] [ContinuousSMul G (ZMod 2)] {φ : G → ZMod 2}
    (h : φ ∈ Z1 G (ZMod 2)) : H1ofFun G φ = H1mk G (ZMod 2) ⟨φ, h⟩ := dif_pos h

/-- Evaluation rule for `H2ofFun` on an actual cocycle. -/
theorem H2ofFun_of_mem {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [DistribMulAction G (ZMod 2)] [ContinuousSMul G (ZMod 2)] {φ : G × G → ZMod 2}
    (h : φ ∈ Z2 G (ZMod 2)) : H2ofFun G φ = H2mk G (ZMod 2) ⟨φ, h⟩ := dif_pos h

end ClassFormers

end GQ2

/-! ### Paper-tag ledger (auto-generated by paperforge; do not edit)

  * eq. (106) = ⟦eq-explicit-corestriction-cup⟧
  * eq. (108) = ⟦eq-normalized-corestriction-two⟧
  * eq. (97) = ⟦eq-two-point-shapiro⟧
  * Lemma 6.1 = ⟦lem-extraspecialconnecting⟧
  * Lemma 6.15 = ⟦lem-orbitshapiro⟧
-/
