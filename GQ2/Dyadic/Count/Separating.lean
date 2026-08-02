/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Opus-5
-/
import GQ2.Dyadic.Count.Separation
import GQ2.Dyadic.Count.Variation

/-!
# Dyadic campaign, ticket CB-5: the word-side suppliers of CB-4's separation forks

CB-4 (`Count/Separation.lean`) stated both separation forks **cup-free**, so that one binder each
serves the arithmetic and the candidate side, and then supplied the arithmetic side
(`isRightSeparating_of_tateDualityG`, `isTwoSeparating_of_tateDualityG`).  This file supplies the
word side.

## What is here

| § | content | status |
|---|---|---|
| 1 | `sepWordN` — the degree-generic `sep_word` | **closed**, no side conditions |
| 2 | the graph hom of a primal/dual pair of cocycles, module-generic | closed |
| 3 | the pair cochain **is** the inflated Heisenberg cocycle | closed |
| 4 | `wordPairing_eq_zero_of_pair_B2` — vanishing of the traced word pairing | closed |
| 5 | **`isRightSeparating_of_selfDualN`** — the `hpartial` fork, candidate side | **closed** |

Section 5 is the ticket's deliverable (b): the degree-generic clone of `ℚ₂`'s
`Phase140GammaA.b1_of_pair_cochain_B2`, which is `Fin 4`-pinned end to end.

## ⚠ The `hsep` fork is *not* closed by §1, and this is a statement about the fork

The ticket scoped (a) as "`IsTwoSeparating` from `IsSelfDualN.cardH2`", by way of the generic
`sep_word`.  §1 delivers the generic `sep_word` — cheaply, and in fact **more cheaply than the
`ℚ₂` ancestor**, since it needs neither the count nor the `2`-torsion hypothesis.  What it does
*not* deliver is `IsTwoSeparating Γ A`, and the obstruction is structural rather than a missing
lemma:

* `IsTwoSeparating Γ A` (`Count/Separation.lean` §5) is a statement about **`H²(Γ, A)`** — a
  continuous `2`-cocycle of the *source group* at **module** coefficients.
* `sepWordN` is a statement about `WordH²(A) = (ρ → A) ⧸ im d¹` — the **word** complex.
* The bridge between them would be a degree-`2` comparison at module coefficients,
  `H²(Γ, A) ↪ WordH²(A)`.  CB-1's comparison (`z1Equiv`/`h1Equiv`) stops at degree `1`; CB-H2's
  degree-`2` rung (`h2Word`) is **scalar-only by construction** — `CentExt` is a central
  extension by `𝔽₂`, `splitU` needs the trivial action, and `obs` lands in `𝔽₂` on the nose
  because the target has two elements.  No such module-coefficient rung exists in the repository.

The `ℚ₂` candidate-side proof of `hsep` (`Phase140/GammaA/Hsep.lean`, `hsep_gammaA`) never forms
`H²(Γ_A, T)` either: it runs the **marking route** — set-lift the marking, read the relator values
in `T`, apply `sep_word` to *those*, correct the marking, descend.  So `sepWordN` is genuinely the
engine that route needs, and the piece still owed is the rest of that route in degree-generic form
(the `exists_relatorFree_marking` / `mlift_of_relatorFree_marking` layer), **or** the
module-coefficient degree-`2` rung.  Either is a ticket, not a lemma.  See §1's docstring for the
precise statement of what `sepWordN` gives and the two ways to consume it.

By contrast the `hpartial` fork needs only degree `1` at module coefficients (for `ξ` and for its
primal partners) and degree `2` at the **scalars** (for the pair cochain, which is `𝔽₂`-valued),
and both of those exist — which is why §5 closes.

## What §5 costs, and what made it affordable

CB-4 flagged the missing pieces for (b) as a degree-generic `obs_inflation` and a degree-generic
`mixedB_eq_relZPair`.  **CB-VAR built both while this ticket was queued**, for the opposite
direction of the same ledger identity:

* `pObsFam_inflation` (`Count/Variation.lean` §4) *is* the degree-generic `MixedBObs.obs_inflation`;
* `pRelZ_kappaHeisN` (§3) *is* the alphabet-generic, `PWord`-valued `mixedB_eq_relZPair`, and it
  needs no `Fin 4` and no `heisEta1` replacement — the `Fin 4`-shaped statement is replaced by one
  `PWord.map_eval` along the structural isomorphism `CentExt kappaHeisN ≅ H(A) ⋊ C`;
* `sum_heisD1_zmod2` (§5a) is the detection functional, and it is what turns "the obstruction lies
  in `im d¹`" into a scalar equation.

So §4 is a **re-use** of CB-VAR's ledger in the contrapositive direction rather than a new
development, and the ticket's predicted `heisEta1`-for-`mixedB_eq_relZPair` substitution never had
to be made: `heisEta1` enters only at the very end, through `IsSelfDualN.pairing`'s own statement.

## What §5 asks a branch for, and at which module

`hpartialN`'s fork is `IsRightSeparating Γ DD.Vmod` — the **`V`-module** over `C = DD.C0`, not the
`T`-module CB-VAR's ledger is instantiated at.  That is not an obstacle: §2–§5 are stated at an
arbitrary finite `C`-module (CB-VAR's `pairHomN` was pinned to `Additive ↥D.T` only by its
instance block, never by its mathematics), and CB-S's payloads (`nCompact_isSelfDualN` and the
other frozen rows) are already module-generic.  What a branch owes is therefore the usual four:
`StokesDuality`/`IsSelfDualN` at `Vmod`, the presentation, `IsWildTwo`, and the four resolutions —
all at CB-VAR §2's **single** Heisenberg level, since `𝔽₂ ⋊ C`, `Vmod ⋊ C` and `Vmod^∨ ⋊ C` are
subgroups of `H(Vmod) ⋊ C`.

Two small measured facts about the binder list, both in the direction of less:

* the dual-side compatibility `hcompatD` is **derived** from `hcompat` (§2's `elemDual_compat`),
  where `ℚ₂` carries both as hypotheses;
* `ContinuousSMul Γ A` is *not* used — only `ContinuousSMul Γ (ElemDual A)` is, and `hpartialN`
  already carries both.

## Numeric leaves

**Nothing in this file reads a count.**  Neither `sepWordN` nor `isRightSeparating_of_selfDualN`
mentions `Nat.card`, `SourceNumerics`, or a degree `n`; `IsSelfDualN` is consumed through clause
**3** (`pairing`) only, never through `cardZ1`, and §1 consumes `StokesDuality`'s `h2_inj` clause
directly.  CB-SG's exponent warning therefore does not apply to anything here — there is no
exponent to check.

## Import discipline

Plain-import.  `Count.Separation` (CB-4, plain) carries the two forks; `Count.Variation` (CB-VAR,
plain) carries the ledger, and through `Count.HTwo`/`Count.Compare` the rung, the comparison and
`IsSelfDualN`.  No new module enters the `Count` closure.

Axioms: no new axioms, no `sorry`, no `decide`.  All **seven** declarations print exactly the
standard three (`propext`, `Classical.choice`, `Quot.sound`) — measured, not budgeted.
-/

namespace GQ2.Dyadic.Count

open GQ2.FoxH GQ2.Dyadic ContCoh
open GQ2.SectionEight GQ2.SectionEight.CentralObstruction

/-! ## §1. The degree-generic `sep_word`

`RStageGammaA.sep_word` (`GQ2/RStage/GammaA.lean:334`) and its Roe twin `sep_word_R`, over an
arbitrary alphabet and relator family: a degree-`2` word cochain killed by every **invariant**
`𝔽₂`-functional is a word coboundary.

Two things are worth recording about the generic proof, because both differ from the `ℚ₂` one:

* **It is a direct implication, not a contradiction.**  `ℚ₂` argues: if `[v] ≠ 0` pick a functional
  `Ψ` on `H²w` with `Ψ[v] ≠ 0`, then use `wTrace_surjective` — a *counting* surjectivity, off
  `IsSelfDual`'s clause 1 — to write `Ψ` as a trace.  Here the hypothesis is turned into an
  extension problem instead: `η²(v)` kills `ker d⁰`, so it descends to `A^∨ ⧸ ker d⁰`, which
  injects into `ι → A^∨`, and `elemDual_extend` (`𝔽₂` is self-injective on finite elementary
  groups) extends it.  That produces exactly the witness `StokesQuasiIso.h2_inj` asks for.
* **Consequently no count and no `2`-torsion hypothesis are used.**  `ℚ₂`'s `sep_word` takes
  `hsd : IsSelfDual t A` and `hA₂ : ∀ a : A, a + a = 0`; this takes `StokesDuality c w A` and
  nothing else.  The `2`-torsion needed by the extension is `2`-torsion of `ι → A^∨`, which is
  automatic (`wordDual_two_torsion`), not a hypothesis on `A`.  In particular the clause of the
  duality package consumed is `h2_inj`, the clause `IsSelfDualN.cardH2` is *derived from*
  (`stokesQuasiIso_card_H2`), so the ticket's "from `IsSelfDualN.cardH2`" is honoured one step
  upstream and with no cardinality in sight. -/

section SepWord

variable {ι ρ : Type*} [Fintype ι] [Fintype ρ] {C : Type*} [Group C]
  {A : Type*} [AddCommGroup A] [DistribMulAction C A] [Finite A]

/-- **The degree-generic `sep_word`.**  If the traced sum `∑ₖ vₖ` of a degree-`2` word cochain is
killed by every `d⁰`-invariant `𝔽₂`-functional on `A`, then `v` is a word coboundary.

`RStageGammaA.sep_word` at an arbitrary alphabet `ι`, an arbitrary relator family `w : ρ → F(ι)`
and an arbitrary finite coefficient module — and with **fewer hypotheses than the `ℚ₂` ancestor**:
no `IsSelfDual` count clause, no `2`-torsion of `A`, no generation, no tame/wild relator
conditions.  The whole input is `StokesDuality`'s `h2_inj`.

The proof is the composition the ticket names: the hypothesis is precisely that `η²(v)` factors
through `d⁰ : A^∨ → (ι → A^∨)`, `elemDual_extend` produces the factorization, and `h2_inj` converts
it into a `d¹`-preimage. -/
theorem sepWordN {c : ι → C} {w : ρ → FreeGroup ι} (hd : StokesDuality c w A) (v : ρ → A)
    (hv : ∀ lam : ElemDual A, heisD0 (A := ElemDual A) c lam = 0 → lam (∑ k, v k) = 0) :
    v ∈ (heisD1 (A := A) c w).range := by
  classical
  set d₀ : ElemDual A →+ (ι → ElemDual A) := heisD0 (A := ElemDual A) c
  set E : ElemDual A →+ ZMod 2 := (heisEta2 v : ElemDual (ElemDual A))
  have hE : ∀ q ∈ d₀.ker, E q = 0 := fun q hq => hv q (AddMonoidHom.mem_ker.mp hq)
  obtain ⟨lam, hlam⟩ := elemDual_extend (A := ι → ElemDual A) (wordDual_two_torsion (A := A))
    (QuotientAddGroup.kerLift d₀) (QuotientAddGroup.kerLift_injective d₀)
    (QuotientAddGroup.lift d₀.ker E hE : ElemDual (ElemDual A ⧸ d₀.ker))
  refine hd.h2_inj v ⟨lam, ElemDual.ext fun q => ?_⟩
  show lam (d₀ q) = E q
  exact hlam (QuotientAddGroup.mk q)

end SepWord

-- CB-VAR's `⊥`-topology on the Heisenberg lift (`Count/Variation.lean` §2).  Its instance
-- attribute is `local`, so it is re-enabled here rather than redeclared.
attribute [local instance] GQ2.Dyadic.Count.heisTopologicalSpace
  GQ2.Dyadic.Count.heisDiscreteTopology

/-! ## §2. The graph hom of a primal/dual pair of cocycles

`Count/Variation.lean` §5b's `pairHomN`, with the recursion's `Additive ↥D.T` turned back into an
arbitrary finite module.  The specialization there is not mathematical — it is only that the
product module `A × A^∨` needs its own instance block, which the recursion's carrier supplies by
name.  Nothing in the construction sees `D`.

The dual compatibility is *derived*, not assumed: the contragredient action is functorial, so a
`ρ`-factorization of the primal action gives one of the dual action (`ℚ₂`'s
`elemDual_smul_eq_of_smul_eq`, which is `private` and `Γ_A`-pinned). -/

section PairHom

variable {Γ : Type} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
  {C : Type} [Group C] [TopologicalSpace C] [DiscreteTopology C] [Finite C]
  {A : Type} [AddCommGroup A] [TopologicalSpace A] [DiscreteTopology A] [Finite A]
  [DistribMulAction C A] [DistribMulAction Γ A]
  [TopologicalSpace (ElemDual A)] [DiscreteTopology (ElemDual A)]
  [TopologicalSpace (WordLift (A × ElemDual A) C)]
  [DiscreteTopology (WordLift (A × ElemDual A) C)]
  (rho : ContinuousMonoidHom Γ C) (hcompat : ∀ (γ : Γ) (a : A), γ • a = rho γ • a)

omit [IsTopologicalGroup Γ] [DiscreteTopology C] [Finite C] [TopologicalSpace A]
  [DiscreteTopology A] [Finite A] [TopologicalSpace (ElemDual A)] [DiscreteTopology (ElemDual A)]
  [TopologicalSpace (WordLift (A × ElemDual A) C)]
  [DiscreteTopology (WordLift (A × ElemDual A) C)] in
include hcompat in
/-- **The dual compatibility, for free.**  If the `Γ`-action on `A` factors through `ρ`, so does
the contragredient action on `A^∨`. -/
theorem elemDual_compat (γ : Γ) (l : ElemDual A) : γ • l = rho γ • l :=
  ElemDual.ext fun a => by
    rw [ElemDual.smul_apply, ElemDual.smul_apply, hcompat γ⁻¹ a, map_inv]

include hcompat in
/-- **The graph hom** `γ ↦ ((z γ, ξ γ), ρ γ)` of a primal/dual pair of continuous crossed
cocycles, into the Heisenberg *base* `(A × A^∨) ⋊ C`.  `Count/Variation.lean`'s `pairHomN` at an
arbitrary module. -/
noncomputable def pairHom (z : Z1 Γ A) (φ : Z1 Γ (ElemDual A)) :
    ContinuousMonoidHom Γ (WordLift (A × ElemDual A) C) where
  toFun γ := ⟨(z.1 γ, φ.1 γ), rho γ⟩
  map_one' := WordLift.ext (Prod.ext (Z1_apply_one z) (Z1_apply_one φ)) (map_one rho)
  map_mul' γ δ := by
    refine WordLift.ext (Prod.ext ?_ ?_) (map_mul rho γ δ)
    · show z.1 (γ * δ) = z.1 γ + rho γ • z.1 δ
      rw [(mem_Z1_iff.mp z.2).2 γ δ, hcompat]
    · show φ.1 (γ * δ) = φ.1 γ + rho γ • φ.1 δ
      rw [(mem_Z1_iff.mp φ.2).2 γ δ, elemDual_compat rho hcompat]
  continuous_toFun := by
    have hg : Continuous fun γ : Γ => (((z.1 γ, φ.1 γ), rho γ) : (A × ElemDual A) × C) :=
      (((mem_Z1_iff.mp z.2).1).prodMk ((mem_Z1_iff.mp φ.2).1)).prodMk rho.continuous_toFun
    exact (continuous_of_discreteTopology (f := (WordLift.equivProd
      (A := A × ElemDual A) (C := C)).symm)).comp hg

omit [IsTopologicalGroup Γ] [Finite C] [Finite A]
  [DiscreteTopology (WordLift (A × ElemDual A) C)] in
@[simp] theorem pairHom_apply (z : Z1 Γ A) (φ : Z1 Γ (ElemDual A)) (γ : Γ) :
    pairHom rho hcompat z φ γ = ⟨(z.1 γ, φ.1 γ), rho γ⟩ := rfl

/-! ## §3. The pair cochain is the Heisenberg cocycle, inflated

`ℚ₂`'s `hunfold` step (`Phase140/GammaA/Hsep.lean`, inside `b1_of_pair_cochain_B2`), which is
also `Count/Variation.lean`'s `varCoc_eq_kappaHeisN` read at a different cochain: `hpartial`'s
pair cochain **is** `varCoc`'s, once the radical edge is replaced by an arbitrary dual cocycle.
The whole content is that the `Γ`-action may be replaced by the `C`-action. -/

omit [IsTopologicalGroup Γ] [Finite C] [Finite A]
  [DiscreteTopology (WordLift (A × ElemDual A) C)] in
include hcompat in
/-- **The pair cochain, unfolded**: `(a, b) ↦ ξ(a)(a · z(b))` is the Heisenberg `2`-cocycle
`kappaHeisN` pulled back along the graph hom. -/
theorem pairCochain_eq_kappaHeisN (z : Z1 Γ A) (φ : Z1 Γ (ElemDual A)) (a b : Γ) :
    (fun p : Γ × Γ => (φ.1 p.1) (p.1 • z.1 p.2)) (a, b)
      = kappaHeisN.κ (pairHom rho hcompat z φ a) (pairHom rho hcompat z φ b) :=
  congrArg (φ.1 a) (hcompat a (z.1 b))

end PairHom

/-! ## §4. The traced word pairing of a coboundary pair cochain vanishes

`ℚ₂`'s `hmix0` step, degree-generic.  Three imported facts and no new mathematics:

* CB-VAR's `pObsFam_inflation` computes the family obstruction of an inflated cocycle as the
  relator obstruction of the pushed marking — this **is** the degree-generic
  `MixedBObs.obs_inflation` the ticket asked for;
* CB-VAR's `pRelZ_kappaHeisN` identifies that with the Heisenberg central coordinate — this is the
  degree-generic `mixedB_eq_relZPair`, and it needed no `heisEta1` substitution: the `Fin 4`
  traced-sum matching is replaced by one `PWord.map_eval` along `CentExt kappaHeisN ≅ H(A) ⋊ C`,
  and `heisEta1` appears only when §5 hands the value to `IsSelfDualN.pairing`;
* CB-H2's `pObsFam_B2_mem_range` plus CB-VAR's `sum_heisD1_zmod2`: a coboundary's obstruction lies
  in `im d¹`, whose traced sum is zero.

Note the asymmetry with CB-VAR §7, which runs the same three facts in the *contrapositive*: there
a nonzero traced sum proves a class nonzero; here a vanishing class proves the traced sum zero. -/

section WordPairing

variable {ι ρ : Type*} [Fintype ι] [Fintype ρ] [DecidableEq ι]
  {Γ : Type} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
  [CompactSpace Γ] [TotallyDisconnectedSpace Γ] [DistribMulAction Γ (ZMod 2)]
  [ContinuousSMul Γ (ZMod 2)]
  {C : Type} [Group C] [TopologicalSpace C] [DiscreteTopology C] [Finite C]
  [DistribMulAction C (ZMod 2)]
  {A : Type} [AddCommGroup A] [TopologicalSpace A] [DiscreteTopology A] [Finite A]
  [DistribMulAction C A] [DistribMulAction Γ A]
  [TopologicalSpace (ElemDual A)] [DiscreteTopology (ElemDual A)]
  [TopologicalSpace (WordLift (ZMod 2) C)] [DiscreteTopology (WordLift (ZMod 2) C)]
  [TopologicalSpace (WordLift (A × ElemDual A) C)]
  [DiscreteTopology (WordLift (A × ElemDual A) C)]
  {gen : ι → Γ} {W : ρ → PWord ι} {w : ρ → FreeGroup ι} {c : ι → C} {J : Set ι}
  (rho : ContinuousMonoidHom Γ C) (hcompat : ∀ (γ : Γ) (a : A), γ • a = rho γ • a)
  (hc : ∀ i, rho (gen i) = c i)

include hcompat hc in
/-- **The traced word pairing of a pair whose cochain is a coboundary vanishes.**

If `(a, b) ↦ ξ(a)(a · z(b))` is a continuous `𝔽₂`-coboundary, then the traced Stokes pairing of
the two evaluated word cocycles is `0`.  This is the whole cohomological content of the
candidate-side `hpartial` fork; §5 is bookkeeping around it. -/
theorem wordPairing_eq_zero_of_pair_B2
    (hpres : IsAdmissibleMarkedPresentation Γ gen W J)
    (hresS : ResolvesAt W w (WordLift (ZMod 2) C)) (hresH : ResolvesAt W w (HeisLift A C))
    (hr : ∀ k, FreeGroup.lift c (w k) = 1) (hend : IsStokesEndpoint w)
    (z : Z1 Γ A) (φ : Z1 Γ (ElemDual A))
    (hB2 : (fun p : Γ × Γ => (φ.1 p.1) (p.1 • z.1 p.2)) ∈ B2 Γ (ZMod 2)) :
    heisEta1 c w (fun i => z.1 (gen i)) (fun i => φ.1 (gen i)) = 0 := by
  classical
  have hmem : (fun p : Γ × Γ => (φ.1 p.1) (p.1 • z.1 p.2)) ∈ Z2 Γ (ZMod 2) := B2_le_Z2 hB2
  set x : Z2 Γ (ZMod 2) := ⟨fun p : Γ × Γ => (φ.1 p.1) (p.1 • z.1 p.2), hmem⟩
  have hobs : pObsFam W gen x
      = fun k => (FreeGroup.lift (heisGen c (fun i => z.1 (gen i))
          (fun i => φ.1 (gen i))) (w k)).z := by
    rw [pObsFam_inflation W gen (pairHom rho hcompat z φ) kappaHeisN x
      (fun a b => pairCochain_eq_kappaHeisN rho hcompat z φ a b)]
    have hbase : (fun i => pairHom rho hcompat z φ (gen i))
        = heisBase c (fun i => z.1 (gen i)) (fun i => φ.1 (gen i)) :=
      funext fun i => WordLift.ext rfl (hc i)
    funext k
    rw [hbase, pRelZ_kappaHeisN, hresH _ k]
  obtain ⟨v, hv⟩ := pObsFam_B2_mem_range (w := w) hpres hresS c (x := x) hB2
  have hsum : ∑ k, pObsFam W gen x k = 0 := by
    rw [← hv]
    exact sum_heisD1_zmod2 hr hend v
  rw [hobs] at hsum
  exact hsum

end WordPairing

/-! ## §5. The candidate-side supplier of the `hpartial` fork

`Phase140GammaA.b1_of_pair_cochain_B2` (`private`, `Fin 4`-pinned through `markC`, `Marking`,
`mixedB`, `z1Equiv` over `Fin 4`, and `prop_5_15`), over an arbitrary alphabet, an arbitrary
relator family, an arbitrary finite coefficient module and an arbitrary presented carrier — and
therefore serving **all five frozen branch families in one theorem**, since none of them appears in
the statement.

Only clause **3** of `IsSelfDualN` is read.  The count clauses are not consumed, so CB-SG's
exponent warning does not apply: there is no cardinality anywhere in the statement or the proof. -/

section RightSeparating

variable {ι ρ : Type*} [Fintype ι] [Fintype ρ] [DecidableEq ι]
  {Γ : Type} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
  [CompactSpace Γ] [TotallyDisconnectedSpace Γ] [DistribMulAction Γ (ZMod 2)]
  [ContinuousSMul Γ (ZMod 2)]
  {C : Type} [Group C] [TopologicalSpace C] [DiscreteTopology C] [Finite C]
  [DistribMulAction C (ZMod 2)]
  {A : Type} [AddCommGroup A] [TopologicalSpace A] [DiscreteTopology A] [Finite A]
  [DistribMulAction C A] [DistribMulAction Γ A] [ContinuousSMul Γ A]
  [TopologicalSpace (ElemDual A)] [DiscreteTopology (ElemDual A)]
  [ContinuousSMul Γ (ElemDual A)]
  [TopologicalSpace (WordLift (ZMod 2) C)] [DiscreteTopology (WordLift (ZMod 2) C)]
  [TopologicalSpace (WordLift A C)] [DiscreteTopology (WordLift A C)]
  [TopologicalSpace (WordLift (ElemDual A) C)] [DiscreteTopology (WordLift (ElemDual A) C)]
  [TopologicalSpace (WordLift (A × ElemDual A) C)]
  [DiscreteTopology (WordLift (A × ElemDual A) C)]
  {gen : ι → Γ} {W : ρ → PWord ι} {w : ρ → FreeGroup ι} {c : ι → C} {J : Set ι}
  (rho : ContinuousMonoidHom Γ C) (hcompat : ∀ (γ : Γ) (a : A), γ • a = rho γ • a)
  (hc : ∀ i, rho (gen i) = c i)

omit [ContinuousSMul Γ A] in
include hcompat hc in
/-- **`IsRightSeparating` from `IsSelfDualN.pairing`** — the candidate-side supplier of CB-4's
`hpartial` fork, and the degree-generic clone of `ℚ₂`'s `b1_of_pair_cochain_B2`.

A continuous dual `1`-cocycle whose pair cochain is a coboundary against *every* `A`-cocycle is
itself a coboundary.  Route: §4 turns each pair-cochain coboundary into a vanishing traced word
pairing; CB-1's `z1Equiv` says every word `1`-cocycle is the evaluation of a continuous one, so
*all* word pairings against `[ξ]` vanish; clause 3's right-slot nondegeneracy kills the class; and
`z1Equiv`-injectivity pulls the resulting word coboundary back to a continuous one.

The three resolutions are at the three targets `𝔽₂ ⋊ C`, `A ⋊ C`, `A^∨ ⋊ C` plus the Heisenberg
lift `H(A) ⋊ C`; CB-VAR §2 shows a *single* level serves all four, since the first three are
subgroups of the fourth. -/
theorem isRightSeparating_of_selfDualN {n : ℕ}
    (hpres : IsAdmissibleMarkedPresentation Γ gen W J) (hwild2 : IsWildTwo J c)
    (hresS : ResolvesAt W w (WordLift (ZMod 2) C)) (hresP : ResolvesAt W w (WordLift A C))
    (hresD : ResolvesAt W w (WordLift (ElemDual A) C))
    (hresH : ResolvesAt W w (HeisLift A C))
    (hsd : IsSelfDualN n c w A) (hend : IsStokesEndpoint w) (hA₂ : ∀ a : A, a + a = 0) :
    IsRightSeparating Γ A := by
  classical
  intro ξ hvan
  have hD₂ : ∀ l : ElemDual A, l + l = 0 := fun l => l.add_self_eq_zero
  have hcompatD := elemDual_compat rho hcompat
  have hr : ∀ k, FreeGroup.lift c (w k) = 1 := fun k =>
    lower_rel (A := A) rho hc hpres hresP k
  set y : ↥(heisD1 (A := ElemDual A) c w).ker :=
    ⟨fun i => ξ.1 (gen i), evalGen_mem_ker rho hcompatD hc hpres hresD ξ⟩ with hydef
  obtain ⟨P, hPval, -, hright⟩ := hsd.pairing
  have hcls0 : stokesH1Mk (heisD0 (A := ElemDual A) c) (heisD1 c w) y = 0 := by
    by_contra hne
    obtain ⟨hcl, hPne⟩ := hright _ hne
    obtain ⟨xw, rfl⟩ := stokesH1Mk_surjective (heisD0 (A := A) c) (heisD1 c w) hcl
    obtain ⟨zc, hzc⟩ := (z1Equiv rho hcompat hc hpres hresP hA₂ hwild2).surjective xw
    refine hPne ?_
    rw [hPval]
    have hxw : (xw : ι → A) = fun i => zc.1 (gen i) := congrArg Subtype.val hzc.symm
    rw [hxw]
    exact wordPairing_eq_zero_of_pair_B2 rho hcompat hc hpres hresS hresH hr hend zc ξ (hvan zc)
  rw [stokesH1Mk_eq_zero_iff] at hcls0
  obtain ⟨m, hm⟩ := hcls0
  refine ⟨m, congrArg Subtype.val
    (show (⟨dZero Γ (ElemDual A) m, B1_le_Z1 ⟨m, rfl⟩⟩ : ↥(Z1 Γ (ElemDual A))) = ξ from ?_)⟩
  refine (z1Equiv rho hcompatD hc hpres hresD hD₂ hwild2).injective
    (Subtype.ext (funext fun i => ?_))
  show gen i • m - m = ξ.1 (gen i)
  rw [hcompatD (gen i) m, hc i]
  exact congrFun hm i

end RightSeparating

end GQ2.Dyadic.Count
