/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Fable 5.1
-/
module

public import TauCeti.NumberTheory.ClassFieldTheory.Local.EulerCharacteristic.Theorem
public import TauCeti.NumberTheory.ClassFieldTheory.FiniteCohomology.DegreeTwo
public import TauCeti.Algebra.Module.ZMod.SMulCommClass
public import TauCeti.Topology.Instances.ZMod
public import GQ2.TauCeti.CohomologyDict

@[expose] public section

/-!
# B7 from Tau Ceti: the local Euler–Poincaré characteristic at `ℚ₂`

Ticket B7 of the Tau Ceti discharge campaign (`docs/orchestration/tauceti-tickets.md`, recon memo
`docs/orchestration/tauceti-t2-recon.md` §B7).  Everything lives in `GQ2.TauCetiBridge`.

The main result, `absGalQ2_localEulerCharacteristic_tauceti`, has the statement of the
`absGalQ2_localEulerCharacteristic` field of `GQ2.LiteratureInputs` verbatim: for a finite discrete
`G_ℚ₂`-module `M` in gq2's typeclass bundle, `H⁰`, `H¹`, `H²` (gq2's explicit continuous cohomology
`GQ2.ContCoh.H0/H1/H2`) are finite and `#H¹ = #H⁰ · #H² · 2^{v₂(#M)}`.

It is proved from Tau Ceti's `TauCeti.ClassFieldTheory.eulerCharacteristic_mixed` (Tate's local
Euler characteristic formula) and `TauCeti.ClassFieldTheory.finite_H` (finiteness in degrees
`≤ 2`), applied to the coefficient object `eulerGalRep M : GalRep (Nat.card M) ℚ_[2]`, which is
`TauCeti.ofDiscreteModule (ZMod (Nat.card M)) (Field.absoluteGaloisGroup ℚ_[2]) M` for the
`ZMod (Nat.card M)`-module structure `zmodNatCardModule M` given by Lagrange's theorem.  The
cardinalities are transported through A2's comparison equivalences `cont0Mod`, `cont1Mod`,
`cont2Mod` (`GQ2/TauCeti/CohomologyDict.lean`), specialised here as `cont0EulerGalRep`,
`cont1EulerGalRep`, `cont2EulerGalRep`.

## Conventions and traps (memo §B7)

* `zmodNatCardModule` is a `def` installed as a *local* instance in this file only (a global
  `Module (ZMod (Nat.card M)) M` instance would be found for every finite additive group).
* `Finite`, `DiscreteTopology` and `ContinuousSMul` on `(eulerGalRep M).V` are not found through
  the `def`; they are supplied by `inferInstanceAs` where needed.
* Under this import closure `Nontrivial ℚ_[2]`/`StrongRankCondition ℚ_[2]` loop through
  `TauCeti.IsAdicComplete.henselianLocalRing`; `finrank_padic_self` is proved with that instance
  switched off locally (`attribute [-instance] … in`) and then used as a plain rewrite.
* Only `M : Type` is reachable: `eulerCharacteristic_mixed` fixes `F : Type`, so
  `GalRep n ℚ_[2] = TopRep.{0}`, and the comparison isomorphisms need `G` and `M` in one universe.
  This matches the `LiteratureInputs` field.
-/

namespace GQ2.TauCetiBridge

/-! ## The coefficient object -/

section Coefficients

/-- A finite abelian group is a `ZMod (Nat.card M)`-module (Lagrange: `Nat.card M • x = 0`).
Not a global instance: install it with `letI`/`attribute [local instance]`. -/
@[instance_reducible] noncomputable def zmodNatCardModule (M : Type*) [AddCommGroup M] [Finite M] :
    Module (ZMod (Nat.card M)) M :=
  haveI : NeZero (Nat.card M) := ⟨Nat.card_pos.ne'⟩
  AddCommGroup.zmodModule fun _ => card_nsmul_eq_zero'

attribute [local instance] zmodNatCardModule

variable (M : Type) [AddCommGroup M] [TopologicalSpace M] [DiscreteTopology M]
  [DistribMulAction AbsGalQ2 M] [Finite M]

/-- The coefficient object of B7: a finite discrete `G_ℚ₂`-module `M`, read as a Tau Ceti
`GalRep (Nat.card M) ℚ_[2]` (a `TopRep (ZMod (Nat.card M)) (Field.absoluteGaloisGroup ℚ_[2])`)
through `TauCeti.ofDiscreteModule`. Its carrier is `M` and its action is the given one
(`eulerGalRep_V`, `eulerGalRep_distribMulAction`, both `rfl`). -/
noncomputable def eulerGalRep : TauCeti.ClassFieldTheory.GalRep (Nat.card M) ℚ_[2] :=
  TauCeti.ofDiscreteModule (ZMod (Nat.card M)) (Field.absoluteGaloisGroup ℚ_[2]) M

theorem eulerGalRep_V : (eulerGalRep M).V = M := rfl

theorem eulerGalRep_distribMulAction :
    (TopRep.distribMulAction (eulerGalRep M) : DistribMulAction AbsGalQ2 M) =
      ‹DistribMulAction AbsGalQ2 M› := rfl

variable [ContinuousSMul AbsGalQ2 M]

/-- `eulerGalRep M` is smooth discrete (Tau Ceti's `ofDiscreteModule_isSmoothDiscrete`). -/
theorem eulerGalRep_isSmoothDiscrete :
    TauCeti.IsSmoothDiscrete (ZMod (Nat.card M)) (eulerGalRep M) :=
  TauCeti.ofDiscreteModule_isSmoothDiscrete _ _ M

/-- Tau Ceti's finiteness theorem at `eulerGalRep M`: `continuousCohomology i (eulerGalRep M)` is
finite for `i ≤ 2`. -/
theorem finite_continuousCohomology_eulerGalRep {i : ℕ} (hi : i ≤ 2) :
    Finite (continuousCohomology i (eulerGalRep M)) :=
  haveI : Finite (eulerGalRep M).V := inferInstanceAs (Finite M)
  TauCeti.ClassFieldTheory.finite_H (Nat.cast_ne_zero.2 Nat.card_pos.ne') (eulerGalRep M)
    (eulerGalRep_isSmoothDiscrete M) hi

attribute [-instance] TauCeti.IsAdicComplete.henselianLocalRing in
/-- `[ℚ₂ : ℚ₂] = 1`, for the `Module ℚ_[2] ℚ_[2]` instance Tau Ceti's Euler characteristic
formula uses (`FinitePadicExtension.toAlgebra ℚ_[2] 2`, which is `Algebra.id`). Proved with
`TauCeti.IsAdicComplete.henselianLocalRing` switched off, since otherwise `Nontrivial ℚ_[2]`
loops (memo §B7). -/
theorem finrank_padic_self :
    @Module.finrank ℚ_[2] ℚ_[2] _ _
      (@Algebra.toModule _ _ _ _ (TauCeti.FinitePadicExtension.toAlgebra ℚ_[2] 2)) = 1 :=
  Module.finrank_self ℚ_[2]

/-- Tau Ceti's Euler characteristic formula at `eulerGalRep M`, with `[ℚ₂ : ℚ₂] = 1` already
substituted. -/
theorem natCard_continuousCohomology_one_eulerGalRep :
    Nat.card (continuousCohomology 1 (eulerGalRep M)) =
      Nat.card (continuousCohomology 0 (eulerGalRep M)) *
        Nat.card (continuousCohomology 2 (eulerGalRep M)) * 2 ^ padicValNat 2 (Nat.card M) := by
  have : Fact (TauCeti.IsSmoothDiscrete (ZMod (Nat.card M)) (eulerGalRep M)) :=
    ⟨eulerGalRep_isSmoothDiscrete M⟩
  have hE := TauCeti.ClassFieldTheory.eulerCharacteristic_mixed 2 ℚ_[2] (Nat.card M)
    Nat.card_pos.ne' (eulerGalRep M) (inferInstanceAs (Finite M))
  rw [finrank_padic_self, one_mul] at hE
  exact hE

/-! ## Comparison with gq2's explicit cohomology (A2 at `R = ZMod (Nat.card M)`) -/

/-- Degree `0`: gq2's `H0 AbsGalQ2 M` against `continuousCohomology 0 (eulerGalRep M)`
(A2's `cont0Mod`). -/
noncomputable def cont0EulerGalRep :
    GQ2.ContCoh.H0 AbsGalQ2 M ≃+ continuousCohomology 0 (eulerGalRep M) :=
  cont0Mod (ZMod (Nat.card M)) AbsGalQ2 M

/-- Degree `1`: gq2's `H1 AbsGalQ2 M` against `continuousCohomology 1 (eulerGalRep M)`
(A2's `cont1Mod`). -/
noncomputable def cont1EulerGalRep :
    GQ2.ContCoh.H1 AbsGalQ2 M ≃+ continuousCohomology 1 (eulerGalRep M) :=
  cont1Mod (ZMod (Nat.card M)) AbsGalQ2 M

/-- Degree `2`: gq2's `H2 AbsGalQ2 M` against `continuousCohomology 2 (eulerGalRep M)`
(A2's `cont2Mod`; `G_ℚ₂` is compact, hence locally compact). -/
noncomputable def cont2EulerGalRep :
    GQ2.ContCoh.H2 AbsGalQ2 M ≃+ continuousCohomology 2 (eulerGalRep M) :=
  cont2Mod (ZMod (Nat.card M)) AbsGalQ2 M

end Coefficients

/-! ## The literature input -/

open GQ2.ContCoh in
/-- **B7 from Tau Ceti**: the local Euler–Poincaré characteristic at `ℚ₂`. For a finite discrete
`G_ℚ₂`-module `M`, the explicit continuous cohomology groups `H⁰`, `H¹`, `H²` are finite and
`#H¹ = #H⁰ · #H² · 2^{v₂(#M)}`. The statement is the type of the
`absGalQ2_localEulerCharacteristic` field of `GQ2.LiteratureInputs`. -/
theorem absGalQ2_localEulerCharacteristic_tauceti (M : Type) [AddCommGroup M] [TopologicalSpace M]
    [DiscreteTopology M] [DistribMulAction AbsGalQ2 M] [ContinuousSMul AbsGalQ2 M]
    [Finite M] :
    Finite (H0 AbsGalQ2 M) ∧ Finite (H1 AbsGalQ2 M) ∧ Finite (H2 AbsGalQ2 M) ∧
      Nat.card (H1 AbsGalQ2 M) =
        Nat.card (H0 AbsGalQ2 M) * Nat.card (H2 AbsGalQ2 M) *
          2 ^ padicValNat 2 (Nat.card M) := by
  have f0 := finite_continuousCohomology_eulerGalRep M (i := 0) (by omega)
  have f1 := finite_continuousCohomology_eulerGalRep M (i := 1) (by omega)
  have f2 := finite_continuousCohomology_eulerGalRep M (i := 2) le_rfl
  refine ⟨Finite.of_equiv _ (cont0EulerGalRep M).toEquiv.symm,
    Finite.of_equiv _ (cont1EulerGalRep M).toEquiv.symm,
    Finite.of_equiv _ (cont2EulerGalRep M).toEquiv.symm, ?_⟩
  rw [Nat.card_congr (cont0EulerGalRep M).toEquiv, Nat.card_congr (cont1EulerGalRep M).toEquiv,
    Nat.card_congr (cont2EulerGalRep M).toEquiv]
  exact natCard_continuousCohomology_one_eulerGalRep M

end GQ2.TauCetiBridge
