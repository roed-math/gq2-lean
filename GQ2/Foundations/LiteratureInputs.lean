/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Opus-4.8, Fable-5, and OpenAI Codex
-/
module

public import GQ2.Statement
public import GQ2.Cohomology
public import GQ2.Reciprocity
public import GQ2.TateDuality
public import GQ2.EvensKahn
public import GQ2.PeripheralAction
public import GQ2.Orientation
public import GQ2.TameQuotient
public import GQ2.TraceForm

@[expose] public section

/-!
# Explicit literature inputs

`LiteratureInputs` bundles the nine classical results used by the proof of the presentation
theorems.  It is deliberately a `Type`-valued class: five inputs are mathematical data rather
than propositions, and the oriented tame quotient depends on the chosen reciprocity datum.

Generic theorems take `[LiteratureInputs]` as an explicit hypothesis.  The legacy axiom-backed
API is recovered separately in `GQ2.Foundations.AxiomInstance` by assembling the original nine
axiom declarations into an instance.  Downstream declarations carry a local
`[LiteratureInputs]` binder exactly when their types or proofs genuinely consume the
bundle.  This keeps the proof-only hypothesis out of unrelated public signatures, makes each
dependency visible at its declaration, and retains concise typeclass inference along the
literature-dependent proof graph.

Lean structure fields cannot quantify over a fresh universe level.  Consequently B7 is stated
here for `M : Type`, which covers every consumer in this development, while the legacy B7 axiom
retains its universe-polymorphic `M : Type*` statement.  The other eight fields transcribe their
legacy declarations without this restriction.
-/

open GQ2.ContCoh

namespace GQ2

/-- The nine cited classical inputs needed by the `Γ_A` and `Γ_R` presentation proofs. -/
class LiteratureInputs where
  /-- B1: topological finite generation of `G_ℚ₂`. -/
  absGalQ2_isTopologicallyFinitelyGenerated :
    ∃ s : Finset AbsGalQ2, (Subgroup.closure (s : Set AbsGalQ2)).topologicalClosure = ⊤
  /-- B7: the local Euler–Poincaré characteristic at `ℚ₂`. -/
  absGalQ2_localEulerCharacteristic (M : Type) [AddCommGroup M] [TopologicalSpace M]
      [DiscreteTopology M] [DistribMulAction AbsGalQ2 M] [ContinuousSMul AbsGalQ2 M]
      [Finite M] :
      Finite (H0 AbsGalQ2 M) ∧ Finite (H1 AbsGalQ2 M) ∧ Finite (H2 AbsGalQ2 M) ∧
        Nat.card (H1 AbsGalQ2 M) =
          Nat.card (H0 AbsGalQ2 M) * Nat.card (H2 AbsGalQ2 M) *
            2 ^ padicValNat 2 (Nat.card M)
  /-- B3c: the marked dyadic orientation and cyclotomic normalization. -/
  dyadicOrientation [CompactSpace AbsGalQ2] [TotallyDisconnectedSpace AbsGalQ2] :
    DyadicOrientation
  /-- B5: local reciprocity for `ℚ₂`. -/
  localReciprocity : LocalReciprocity
  /-- B6: local Tate duality over finite extensions of `ℚ₂`. -/
  tateDualityAt (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
      (n : ℕ) [NeZero n] [DistribMulAction G (MuN n)] [ContinuousSMul G (MuN n)]
      (hloc : IsLocalDualizingGroup G n) : TateDualityG G n
  /-- B8: the cyclotomic action on peripheral generators. -/
  peripheralCyclotomicAction : PeripheralCyclotomicAction
  /-- B9: the relative Stiefel–Whitney identity over finite dyadic bases. -/
  relativeStiefelWhitney_dyadic
      (k : IntermediateField ℚ_[2] (AlgebraicClosure ℚ_[2])) [FiniteDimensional ℚ_[2] k]
      (d : (↥k)ˣ) (δ β : AlgebraicClosure ℚ_[2])
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
      (swOne k (traceFormTwisted k δ ↑a) =
          swOne k (traceFormOne k δ) + corH1 htriv hUo hidx hs α hα hαc) ∧
        (swTwo k htriv (traceFormTwisted k δ ↑a) =
          swTwo k htriv (traceFormOne k δ) +
            swOne k (traceFormOne k δ) ⌣[htriv] corH1 htriv hUo hidx hs α hα hαc +
              evensNormH2 htriv hUo hidx hs α hα hαc)
  /-- B10: the tame quotient, oriented against the bundled reciprocity datum. -/
  tameQuotient : OrientedTameQuotient localReciprocity
  /-- B11a: the Hilbert-symbol norm criterion over finite dyadic bases. -/
  hilbertSymbol_normCriterion_finiteDyadic
      (k : IntermediateField ℚ_[2] (AlgebraicClosure ℚ_[2])) [FiniteDimensional ℚ_[2] k]
      (htriv : ∀ (g : k.fixingSubgroup) (m : ZMod 2), g • m = m) :
      ∀ a b : (↥k)ˣ,
        kummerClassK k a ⌣[htriv] kummerClassK k b = 0 ↔
          ∃ x y : ↥k, (b : ↥k) = x ^ 2 - (a : ↥k) * y ^ 2

end GQ2
