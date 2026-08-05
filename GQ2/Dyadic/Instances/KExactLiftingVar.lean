/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Opus-5
-/
import GQ2.Dyadic.Instances.KExactLifting

/-!
# The half-torsor clause at `G_K`  (package P5, clause 2)

`ExactLiftingSemantics`'s second conjunct — `2 · #{central M-lifts} = #M-lifts` — over an
arbitrary profinite source carrying Tate duality at `2`, and its specialization to `G_K`.

## What was actually owed

`GQ2/Dyadic/Instances/KSupply.lean`'s `lem86_galK` already reduces the clause at `G_K` to a single
existential: a crossed `T`-cocycle whose **variation class is nonzero** in `H²(G_K, 𝔽₂)`
(`Count.lem86N` supplies everything else from `tfg_galK` and `card_H2_zmodTwo_galK`).  The `ℚ₂`
ancestor of that existential is `RadicalEdgeLocal.exists_good_twist`
(`GQ2/RadicalEdge/Local.lean:475`, `private`; public entry `half_torsor_local`).

## Degree-genericity: the answer is *yes*, and for a structural reason

The `ℚ₂` twist argument uses **exactly one** arithmetic input — perfectness of B6's `(1,1)`
pairing on the `ρ`-conjugation module — and *no* local Euler characteristic, *no* `#H² = 2`, and
no degree anywhere.  So unlike the lift count of `KExactLifting.lean`, this clause needs **no
Euler correction at all**: it is degree-generic on the nose, and the `d = 1` proof is the general
proof.

The port is nonetheless not a retype, because the campaign has since factored both halves of the
`ℚ₂` argument into `Γ`-generic public pieces, and they meet here:

* CB-VAR's `phiVar` (`GQ2/Dyadic/Count/Variation.lean` §6) is the shifted-edge dual `1`-cocycle
  `γ ↦ (s ↦ ε̄(ργ)(γ⁻¹ · s))`, already stated over an abstract `Γ`, with `phiVar_mem_Z1` and
  `phiVar_ne_zero` (the latter is the `NoDescent` contraposition, `Γ`-free);
* CB-SG's `IsRightSeparating Γ A` (`GQ2/Dyadic/Count/Separation.lean` §2) is the *cup-free*
  statement of `(1,1)` perfectness, and `isRightSeparating_of_tateDualityG` supplies it from a
  `TateDualityG` bundle alone — its docstring already records "**No `LocalEulerChar`, no
  degree**".

Reading them against each other is the whole proof: `IsRightSeparating` says that a dual cocycle
pairing trivially against *every* primal cocycle is a coboundary; `phiVar_ne_zero` says the
shifted edge is not one; so some primal `z ∈ Z¹(Γ, T)` pairs nontrivially, and its pair cochain
`(a, b) ↦ φ(a)(a · z(b))` **is**, on the nose, the variation cochain of the `T`-cocycle
`tcocycleEquivZ1.symm z`.  That last identification is `varCoc_pairCochain` below; the `ℚ₂` file
proves it as `cup11Fun_shiftedEdge_eq_varCoc` through `MuDual`, which the cup-free route avoids.

The word-side twin of this theorem is CB-VAR's `exists_nonzero_varCoc`, which reaches the same
conclusion from a presentation plus a Stokes payload.  Neither implies the other: `G_K` has no
presentation (that is what the campaign is proving) and the candidate has no Tate bundle.

Axioms: both sections are parametrized over the bundle `Dl` (and, in §2, over `tfg` and the
scalar `H²` count), so every declaration prints exactly the standard three (measured).  B6 and
B1 enter only at the `G_K` instantiation, in `KExactLiftingGalK.lean`.  No new axiom, no
`sorry`.
-/

namespace GQ2.Dyadic.Count

open GQ2 GQ2.SectionEight GQ2.SectionEight.CentralObstruction
open GQ2.FoxH ContCoh GQ2.SectionEight.RadicalEdgeGammaA
open LiftingDualityG

/-! ## §1 The nonzero variation class from Tate duality -/

section GoodTwist

variable {Bg : Type} [Group Bg] [TopologicalSpace Bg] [DiscreteTopology Bg] [Finite Bg]
  {D : RadicalCoverData Bg}
  {Γ : Type} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
  [DistribMulAction Γ (MuN 2)] [ContinuousSMul Γ (MuN 2)]
  [DistribMulAction Γ (ZMod 2)]
  [TopologicalSpace (Additive ↥D.T)] [DiscreteTopology (Additive ↥D.T)]
  [DistribMulAction Γ (Additive ↥D.T)] [ContinuousSMul Γ (Additive ↥D.T)]
  [DistribMulAction Γ (ElemDual (Additive ↥D.T))]
  [ContinuousSMul Γ (ElemDual (Additive ↥D.T))]
  (S : TComplement D) (rho : ContinuousMonoidHom Γ (Bg ⧸ D.M))
  (hcompat : ∀ (γ : Γ) (a : Additive ↥D.T), γ • a = rho γ • a)
  (hcompatD : ∀ (γ : Γ) (l : ElemDual (Additive ↥D.T)), γ • l = rho γ • l)

omit [IsTopologicalGroup Γ] [DistribMulAction Γ (MuN 2)] [ContinuousSMul Γ (MuN 2)]
  [DistribMulAction Γ (ZMod 2)] [ContinuousSMul Γ (Additive ↥D.T)]
  [DistribMulAction Γ (ElemDual (Additive ↥D.T))]
  [ContinuousSMul Γ (ElemDual (Additive ↥D.T))] in
include hcompat in
/-- **The variation cochain *is* the `(1,1)` pair cochain of the shifted edge.**

For `z ∈ Z¹(Γ, T)` and `u` its `T`-cocycle avatar, `varCoc u (a, b) = φ(a)(a · z(b))` where `φ`
is CB-VAR's `phiVar`.  Both sides are `edgeQ D S (ρa) (z b)` after one `inv_smul_smul`; this is
the cup-free form of the `ℚ₂` file's `cup11Fun_shiftedEdge_eq_varCoc`. -/
theorem varCoc_pairCochain (z : ↥(Z1 Γ (Additive ↥D.T))) :
    varCoc D rho S ((tcocycleEquivZ1 rho hcompat).symm z)
      = fun p : Γ × Γ => (phiVar S rho p.1) (p.1 • z.1 p.2) := by
  funext p
  obtain ⟨a, b⟩ := p
  show edgeQ D S (rho a) ⟨((Additive.toMul (z.1 b) : ↥D.T) : Bg), _⟩
    = (phiVar S rho a) (a • z.1 b)
  rw [phiVar_apply, inv_smul_smul]

include hcompat hcompatD in
/-- **The nonzero variation class over any source carrying Tate duality at `2`** — the `Γ`-generic
form of `RadicalEdgeLocal.exists_good_twist`.

Given a radical cover that does not descend and a surjection `ρ : Γ ↠ Bg ⧸ M`, there is a crossed
`T`-cocycle whose variation class is nonzero in `H²(Γ, 𝔽₂)`.

**Degree-free.**  The only arithmetic input is `Dl`; no `LocalEulerChar` appears, so the exponent
caveat that governs the lift count (`KExactLifting.lean`) has no analogue here. -/
theorem exists_nonzero_varCoc_of_tateDualityG (Dl : TateDualityG Γ 2)
    (hedge : D.NoDescent) (hρ : Function.Surjective rho) :
    ∃ u : TCocycle D rho,
      H2mk Γ (ZMod 2) ⟨varCoc D rho S u, varCoc_mem_Z2 D rho S smul_zmod2 u⟩ ≠ 0 := by
  classical
  by_contra hall
  push Not at hall
  have hT₂ : ∀ a : Additive ↥D.T, a + a = 0 := radT_add_self D
  have hpairEq : ∀ (γ : Γ) (a : Additive ↥D.T) (lam : ElemDual (Additive ↥D.T)),
      dualEval (Additive ↥D.T) (γ • a) (γ • lam) = γ • dualEval (Additive ↥D.T) a lam := by
    intro γ a lam
    rw [dualEval_apply, dual_smul_apply rho hcompat hcompatD, inv_smul_smul, dualEval_apply,
      smul_zmod2]
  have hsep : IsRightSeparating Γ (Additive ↥D.T) :=
    isRightSeparating_of_tateDualityG Dl hT₂ smul_zmod2 hpairEq
  have hpairAll : ∀ zc : ↥(Z1 Γ (Additive ↥D.T)),
      (fun p : Γ × Γ => (phiVar S rho p.1) (p.1 • zc.1 p.2)) ∈ B2 Γ (ZMod 2) := by
    intro zc
    have h0 := hall ((tcocycleEquivZ1 rho hcompat).symm zc)
    rw [H2mk_eq_zero_iff] at h0
    rw [← varCoc_pairCochain S rho hcompat zc]
    exact h0
  obtain ⟨n, hn⟩ := hsep ⟨phiVar S rho, phiVar_mem_Z1 S rho hcompat hcompatD⟩ hpairAll
  exact phiVar_ne_zero S rho hcompat hcompatD hρ hedge
    ((QuotientAddGroup.eq_zero_iff _).mpr (AddSubgroup.mem_addSubgroupOf.mpr ⟨n, hn⟩))

end GoodTwist

/-! ## §2 The half-torsor clause, over the abstract carrier

`Count.lem86N` turns the witness into the count; every other input it takes (`tfg`, `#H² = 2`) is
already a theorem at `G_K`. -/

section HalfTorsor

variable {Bg : Type} [Group Bg] [TopologicalSpace Bg] [DiscreteTopology Bg] [Finite Bg]
  {Γ : Type} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [CompactSpace Γ]
  [TotallyDisconnectedSpace Γ]
  [DistribMulAction Γ (MuN 2)] [ContinuousSMul Γ (MuN 2)]
  [DistribMulAction Γ (ZMod 2)] [ContinuousSMul Γ (ZMod 2)]

omit [ContinuousSMul Γ (ZMod 2)] in
/-- **The `SourceDataN.lem86` value over any source carrying Tate duality at `2`.**

`NoDescent` plus `Dl` produce the variation witness (§1); `Count.lem86N` counts.  The `ρ`-side
module instances are built here rather than assumed, so the statement has the exact shape of the
second `ExactLiftingSemantics` conjunct. -/
theorem lem86_of_tateDualityG (Dl : TateDualityG Γ 2)
    (tfg : ∃ s : Finset Γ, (Subgroup.closure (s : Set Γ)).topologicalClosure = ⊤)
    (hcardH2 : Nat.card (H2 Γ (ZMod 2)) = 2)
    (D : RadicalCoverData Bg) (hedge : D.NoDescent)
    (rho : ContinuousMonoidHom Γ (Bg ⧸ D.M)) (hρ : Function.Surjective rho) :
    2 * Nat.card {f : MLifts D rho // f.Central} = Nat.card (MLifts D rho) := by
  classical
  haveI := discreteTopology_quotient D
  letI : TopologicalSpace (Additive ↥D.T) := ⊥
  haveI : DiscreteTopology (Additive ↥D.T) := ⟨rfl⟩
  letI : DistribMulAction Γ (Additive ↥D.T) :=
    DistribMulAction.compHom _ rho.toMonoidHom
  have hcompat : ∀ (γ : Γ) (a : Additive ↥D.T), γ • a = rho γ • a := fun _ _ => rfl
  haveI : ContinuousSMul Γ (Additive ↥D.T) := by
    constructor
    have hfac : (fun p : Γ × Additive ↥D.T => p.1 • p.2) =
        (fun p : (Bg ⧸ D.M) × Additive ↥D.T => p.1 • p.2) ∘
          (fun p : Γ × Additive ↥D.T => (rho p.1, p.2)) := rfl
    rw [hfac]
    exact continuous_of_discreteTopology.comp
      ((rho.continuous_toFun.comp continuous_fst).prodMk continuous_snd)
  have hcompatD : ∀ (γ : Γ) (l : ElemDual (Additive ↥D.T)), γ • l = rho γ • l := by
    intro γ l
    refine DFunLike.ext _ _ fun a => ?_
    rw [ElemDual.smul_apply, ElemDual.smul_apply, hcompat, map_inv]
  haveI : ContinuousSMul Γ (ElemDual (Additive ↥D.T)) := by
    constructor
    have hfac : (fun p : Γ × ElemDual (Additive ↥D.T) => p.1 • p.2) =
        (fun p : (Bg ⧸ D.M) × ElemDual (Additive ↥D.T) => p.1 • p.2) ∘
          (fun p : Γ × ElemDual (Additive ↥D.T) => (rho p.1, p.2)) := by
      funext p
      exact hcompatD p.1 p.2
    rw [hfac]
    exact continuous_of_discreteTopology.comp
      ((rho.continuous_toFun.comp continuous_fst).prodMk continuous_snd)
  obtain ⟨S⟩ := tComplement_nonempty D
  obtain ⟨u, hvar⟩ :=
    exists_nonzero_varCoc_of_tateDualityG S rho hcompat hcompatD Dl hedge hρ
  exact lem86N tfg hcardH2 D rho S u hvar

end HalfTorsor

end GQ2.Dyadic.Count
