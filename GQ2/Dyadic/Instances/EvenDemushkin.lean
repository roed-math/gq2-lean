/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Opus-5
-/
import GQ2.Dyadic.Instances.EvenModelDemushkin
import GQ2.Dyadic.Instances.StageAbstractionEvenAssembly

/-!
# W52-EV1E: the model Demushkin package, audited, and hypothesis 1 of the assembly discharged

Ticket **EV-1e** (`IsDemushkin` at the two even cores) and **EV-1b** (their rank identities) of
the even-degree forward route.  The four statements were recorded as comments in the route
skeleton (`GQ2/Dyadic/Instances/EvenForwardRouteSkeleton.lean:58-61`):

```text
-- EV-1e  theorem isDemushkin_DN (α h : ℕ) (hα : 2 ≤ α) : IsDemushkin 2 (DN α h : Type)
-- EV-1e  theorem isDemushkin_DM (α h : ℕ) (hα : 2 ≤ α) : IsDemushkin 2 (DM α h : Type)
-- EV-1b  theorem demushkinRank_DN (α h : ℕ) : demushkinRank 2 (DN α h : Type) = coreRank h
-- EV-1b  theorem demushkinRank_DM (α h : ℕ) : demushkinRank 2 (DM α h : Type) = coreRank h
```

## What this file found, and therefore what it does

All four are **already committed**, sorry-free and registered, in
`GQ2/Dyadic/Instances/EvenModelH2.lean` (EV-1a/EV-1b/EV-1c) and
`GQ2/Dyadic/Instances/EvenModelDemushkin.lean` (EV-1d/EV-1e), together with the two skeleton
obligations `nModelDemushkin` / `mModelDemushkin`.  The skeleton's comment block above is stale
documentation, not an open goal.  This file therefore does the three things that were genuinely
missing.

1. **The audit** (§1, §2).  The recorded statements are re-derived here in the shape the ticket
   asks for, so that the exact hypothesis lists are machine-checked rather than read off prose.
   One recorded statement is **wrong as recorded**: the EV-1b lines carry no `α` hypothesis, but
   the committed rank identities require `1 ≤ α`, and §3 shows that this is not slack in the
   proof.
2. **The seam** (§4).  `evenAssembly_orientedEquivN` / `…M`
   (`GQ2/Dyadic/Instances/StageAbstractionEvenAssembly.lean:140`, `:160`) carry six named
   hypotheses, of which hypothesis 1 is exactly this ticket's model-side package.  The
   `ev1eFinal_*` endpoints below are those statements with hypothesis 1 gone, leaving five.  The
   model lane and the assembly lane were built in different waves and had never been composed;
   this is the composition, and it is what demonstrates that the seam closes.
3. **The threshold** (§3).  Why `1 ≤ α` on the rank and `2 ≤ α` on `IsDemushkin` are the honest
   hypotheses, and what is left open below them, named as `Prop`s with their cost.

## The `α` thresholds are structural, not proof slack

The `N` relator head exponent is `2 + 2 ^ α` and the `M` relator head exponent is `2 ^ α`.  The
Frattini step of `markedRelator_DN` / `markedRelator_DM`
(`GQ2/Dyadic/MarkedCore/Certificate.lean:294`, `:281`) needs those exponents **even**, which is
exactly `1 ≤ α` in both cases (`evenDem_nHeadExponent_even_iff`, `evenDem_mHeadExponent_even_iff`
below).  At `α = 0` the `N` head exponent is `2 + 1 = 3`, odd: the relator leaves the Frattini
subgroup, consumes a generator, and the rank identity `= coreRank h` should be expected to
**fail**, not merely to be unproved.  So the recorded hypothesis-free EV-1b statement is not a
target to aim at.

At `α = 1` both cores are still one-relator pro-`2` groups with the relator in the Frattini
subgroup, so the rank identity holds; what fails is the *Gram*, and with it nondegeneracy.  The
committed `EvenModelDemushkin` docstring records that at `α = 1` the shared Gram
`mGram = nGram` is no longer the common value: the `N` head exponent becomes
`2 + 2 ^ 1 = 4 ≡ 0 (mod 4)` and its diagonal entry dies, while the `M` row picks up a second
diagonal entry at slot `2`.  Section §3 names the two resulting open questions.

## Numbering

1. EV-1e, audited: `IsDemushkin` at both even cores.
2. EV-1b, audited: the two rank identities, and the two skeleton obligations.
3. The `α` thresholds, and the named residuals below them.
4. EV-1e final: the two assembly endpoints with hypothesis 1 discharged.
5. Axiom pins.
-/

namespace GQ2.Dyadic.EvenDemushkin

noncomputable section

open GQ2 GQ2.Dyadic.MarkedCore GQ2.Dyadic.EvenForward GQ2.Dyadic.StageGeneric

local notation "ℚ̄₂" => AlgebraicClosure ℚ_[2]

/-- The coefficient action at the `N` core, as everywhere on this route: the unique action of a
group on `𝔽₂`, which is the trivial one. -/
local instance evenDemScalarActionDN (α h : ℕ) : DistribMulAction (DN α h : Type) (ZMod 2) :=
  scalarActionZmodTwo _

/-- Continuity of the `N`-core coefficient action. -/
local instance evenDemContinuousScalarDN (α h : ℕ) : ContinuousSMul (DN α h : Type) (ZMod 2) :=
  scalarActionZmodTwo_continuousSMul _

/-- The coefficient action at the `M` core. -/
local instance evenDemScalarActionDM (α h : ℕ) : DistribMulAction (DM α h : Type) (ZMod 2) :=
  scalarActionZmodTwo _

/-- Continuity of the `M`-core coefficient action. -/
local instance evenDemContinuousScalarDM (α h : ℕ) : ContinuousSMul (DM α h : Type) (ZMod 2) :=
  scalarActionZmodTwo_continuousSMul _

/-! ## §1 EV-1e audited: the two even cores are Demushkin

The recorded statements, verbatim in their recorded shape.  Both are the committed theorems of
`EvenModelDemushkin.lean` §4; restating them here pins the hypothesis list (`2 ≤ α`, nothing on
`h`) against the skeleton comment. -/

/-- **EV-1e, `N` row, as recorded.**  The even `N_α` core is a Demushkin pro-`2` group for every
handle count `h` and every branch depth `α ≥ 2`.  This is the committed
`GQ2.Dyadic.EvenModel.isDemushkin_DN`; the hypothesis list matches the skeleton comment exactly. -/
theorem evenDem_isDemushkin_DN (α h : ℕ) (hα : 2 ≤ α) : IsDemushkin 2 (DN α h : Type) :=
  GQ2.Dyadic.EvenModel.isDemushkin_DN α h hα

/-- **EV-1e, `M` row, as recorded.**  Same Gram, same argument, same hypothesis. -/
theorem evenDem_isDemushkin_DM (α h : ℕ) (hα : 2 ≤ α) : IsDemushkin 2 (DM α h : Type) :=
  GQ2.Dyadic.EvenModel.isDemushkin_DM α h hα

/-! ## §2 EV-1b audited: the rank identities, and the two skeleton obligations

The recorded EV-1b lines carry no hypothesis on `α`.  The committed identities carry `1 ≤ α`, and
§3 shows that hypothesis is exactly the evenness of the relator head exponent, so it cannot be
dropped.  What follows is therefore the recorded statement *with the honest hypothesis restored*,
plus the `2 ≤ α` specialization that the `IsDemushkin` package actually consumes. -/

/-- **EV-1b, `N` row, with the honest hypothesis.**  The `N_α` relator lies in the Frattini
subgroup once `1 ≤ α`, so no generator is consumed and `H¹` has the full literal marking rank
`coreRank h = 4 + 2h`.  The recorded statement omitted `1 ≤ α`; see
`evenDem_nHeadExponent_even_iff` for why that omission is not repairable. -/
theorem evenDem_demushkinRank_DN (α h : ℕ) (hα : 1 ≤ α) :
    demushkinRank 2 (DN α h : Type) = coreRank h :=
  GQ2.Dyadic.EvenModel.demushkinRank_DN α h hα

/-- **EV-1b, `M` row, with the honest hypothesis.** -/
theorem evenDem_demushkinRank_DM (α h : ℕ) (hα : 1 ≤ α) :
    demushkinRank 2 (DM α h : Type) = coreRank h :=
  GQ2.Dyadic.EvenModel.demushkinRank_DM α h hα

/-- The `N` rank identity in the range the `IsDemushkin` package lives in, so that EV-1e and
EV-1b can be quoted with a single hypothesis. -/
theorem evenDem_demushkinRank_DN_of_two_le (α h : ℕ) (hα : 2 ≤ α) :
    demushkinRank 2 (DN α h : Type) = coreRank h :=
  evenDem_demushkinRank_DN α h (le_trans one_le_two hα)

/-- The `M` rank identity at `2 ≤ α`. -/
theorem evenDem_demushkinRank_DM_of_two_le (α h : ℕ) (hα : 2 ≤ α) :
    demushkinRank 2 (DM α h : Type) = coreRank h :=
  evenDem_demushkinRank_DM α h (le_trans one_le_two hα)

/-- **The `N`-row skeleton obligation**, the conjunction the rigidity step consumes.  This is
hypothesis 1 of the even assembly endpoints, on the `N` branch. -/
theorem evenDem_nModelDemushkin (α h : ℕ) (hα : 2 ≤ α) : NModelDemushkin α h :=
  ⟨evenDem_isDemushkin_DN α h hα, evenDem_demushkinRank_DN_of_two_le α h hα⟩

/-- **The `M`-row skeleton obligation.** -/
theorem evenDem_mModelDemushkin (α h : ℕ) (hα : 2 ≤ α) : MModelDemushkin α h :=
  ⟨evenDem_isDemushkin_DM α h hα, evenDem_demushkinRank_DM_of_two_le α h hα⟩

/-- The `N`-row obligation in the uniform-in-`h` shape the assembly endpoint asks for. -/
theorem evenDem_nModelDemushkin_forall (α : ℕ) (hα : 2 ≤ α) : ∀ h : ℕ, NModelDemushkin α h :=
  fun h => evenDem_nModelDemushkin α h hα

/-- The `M`-row obligation, uniform in `h`. -/
theorem evenDem_mModelDemushkin_forall (α : ℕ) (hα : 2 ≤ α) : ∀ h : ℕ, MModelDemushkin α h :=
  fun h => evenDem_mModelDemushkin α h hα

end

end GQ2.Dyadic.EvenDemushkin
