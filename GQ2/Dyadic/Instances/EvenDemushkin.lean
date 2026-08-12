/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Opus-5
-/
import GQ2.Dyadic.Instances.EvenModelDemushkin
import GQ2.Dyadic.Instances.StageAbstractionEvenAssembly
import GQ2.Dyadic.MarkedCore.MFrameExists
import GQ2.Dyadic.MarkedCore.NFrameExists

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
subgroup, so the rank identity holds; what changes is the *Gram*, and wave 70 computes it:
nondegeneracy survives on both rows.  The
committed `EvenModelDemushkin` docstring records that at `α = 1` the shared Gram
`mGram = nGram` is no longer the common value: the `N` head exponent becomes
`2 + 2 ^ 1 = 4 ≡ 0 (mod 4)` and its diagonal entry dies, while the `M` row picks up a second
diagonal entry at slot `2`.  Both resulting matrices are nondegenerate, so §3's two questions
are now settled (wave 70): see the residual docstrings below.

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

/-! ## §3 The `α` thresholds, and what is open below them

Two independent thresholds are in play, and conflating them is what produced the wrong recorded
EV-1b statement.

* `1 ≤ α` is the **Frattini** threshold: the relator head exponent must be even, or the relator
  is not a product of squares and commutators, and the abelianization loses a generator.  This is
  the hypothesis of `markedRelator_DN` / `markedRelator_DM`, hence of `H¹` and hence of the rank.
* `2 ≤ α` is the **Gram** threshold: it is what pins the common relator Gram
  `mGram = nGram` and so what makes one nondegeneracy argument serve both rows.  This is the
  hypothesis of `IsDemushkin`.

The first two theorems below identify the Frattini threshold exactly, so that the recorded
hypothesis-free EV-1b statement is seen to be unattainable rather than merely unproved. -/

/-- **The `N` Frattini threshold, exactly.**  The `N_α` relator head exponent `2 + 2 ^ α` is even
if and only if `1 ≤ α`.  This is the arithmetic step inside `markedRelator_DN`
(`GQ2/Dyadic/MarkedCore/Certificate.lean:294`), isolated: at `α = 0` the exponent is `3`, the
relator is not in the Frattini subgroup, and the marked-relator bundle that the whole `H¹`
computation runs on does not exist.  Hence the recorded EV-1b statement, which carries no `α`
hypothesis, is not a repairable target. -/
theorem evenDem_nHeadExponent_even_iff (α : ℕ) : (∃ k, 2 + 2 ^ α = 2 * k) ↔ 1 ≤ α := by
  constructor
  · rintro ⟨k, hk⟩
    by_contra hcon
    have hα : α = 0 := by omega
    rw [hα, pow_zero] at hk
    omega
  · intro hα
    obtain ⟨j, rfl⟩ : ∃ j, α = j + 1 := ⟨α - 1, by omega⟩
    exact ⟨1 + 2 ^ j, by rw [pow_succ]; ring⟩

/-- **The `M` Frattini threshold, exactly.**  The `M_α` relator head exponent `2 ^ α` is even if
and only if `1 ≤ α`, the same threshold on the same grounds. -/
theorem evenDem_mHeadExponent_even_iff (α : ℕ) : (∃ k, 2 ^ α = 2 * k) ↔ 1 ≤ α := by
  constructor
  · rintro ⟨k, hk⟩
    by_contra hcon
    have hα : α = 0 := by omega
    rw [hα, pow_zero] at hk
    omega
  · intro hα
    obtain ⟨j, rfl⟩ : ∃ j, α = j + 1 := ⟨α - 1, by omega⟩
    exact ⟨2 ^ j, by rw [pow_succ]; ring⟩

/-! ### The `α = 1` asymmetry, machine-checked

The two rows are *not* symmetric at `α = 1`, and the committed frame layer already says so
without any Gram computation.  The three statements below are the evidence, restated here from
`MFrameExists.lean` and `NFrameExists.lean` so that the residual `Prop`s that follow are read
against a fact rather than against an expectation: at `α = 1` the `M` core still has a frame, and
with it a computed `q`-invariant, while the `N` core provably has none.  This is exactly the
asymmetry pattern to expect of R1 and R2, and it is why R2 is stated in the positive direction
and R1 in the negative. -/

/-- **The `M` core keeps its `q`-invariant at `α = 1`.**  `MFrame` exists from `1 ≤ α` on, so the
torsion count goes through at `α = 1` unchanged.  The `M` row is therefore not obviously damaged
at the Gram threshold, only unproved there. -/
theorem evenDem_demushkinQ_DM_alphaOne (h : ℕ) : demushkinQ (DM 1 h : Type) = 2 :=
  mFrameExists_demushkinQ_DM le_rfl h

/-- **The `N` core has no frame at `α = 1`.**  `NFrame 1 h` is *empty*: the `N` abelianization at
`α = 1` is not `ℤ/2 ⊕ ℤ₂ ^ (3 + 2h)`, because the head exponent `2 + 2 ^ 1 = 4` puts the torsion
generator in the wrong place.  This is a committed theorem, not a conjecture, and it is the
structural reason to expect R1. -/
theorem evenDem_nFrame_isEmpty_alphaOne (h : ℕ) : IsEmpty (NFrame 1 h) :=
  nFrameExists_isEmpty_one h

/-- **The `N` frame threshold, exactly.**  `2 ≤ α` is not conservative on the `N` row: it is
equivalent to the frame existing at all.  Contrast `nonempty_mFrame`, which needs only `1 ≤ α`. -/
theorem evenDem_nFrame_nonempty_iff (α h : ℕ) : Nonempty (NFrame α h) ↔ 2 ≤ α :=
  nFrameExists_nonempty_iff α h

/-- **Residual R1 (`N` at `α = 1`), REFUTED (wave 70).**  This `Prop` is **false**, and is kept
only so the refutation has something to name.  `Instances/EvenAlphaOne.lean` computes the
`α = 1` `N` Gram directly and proves `IsDemushkin 2 (DN 1 h)` for every `h`
(`evenAlphaOne_isDemushkin_DN`), hence `¬ EvenDemResidualAlphaOneN`
(`evenAlphaOne_residualN_false`).

What the original reasoning got right: the head exponent is `2 + 2 ^ 1 = 4 ≡ 0 (mod 4)`, so the
`(0,0)` Gram entry does die.  What it got wrong: the resulting matrix
`[[0,1,0,0],[1,0,0,0],[0,0,0,1],[0,0,1,0]]` is two hyperbolic blocks, which is *alternating*
and **nondegenerate**, not degenerate.  Alternating was read as degenerate.
`evenDem_nFrame_isEmpty_alphaOne` is likewise not evidence against Demushkin-ness: the frame
layer represents a `ℤ/2` torsion slot, and an alternating cup form is the mod-`2` signature of
`q ≢ 2`.  ⚠ The `q`-invariant at `α = 1` is still **uncomputed**: `demushkinQ` is a torsion
count on the abelianization, independent of `IsDemushkin`, and the committed route to it runs
through `NFrame`, which is provably empty here, so that route is structurally unavailable
rather than merely unproved.

The superseded original reasoning follows, for the record.  Nothing in the committed development
decides the Demushkin question itself, in either direction.

Cost to close: the `α = 1` `N` Gram has to be computed afresh (the committed
`diagCoeff_two_pow` route needs `2 ≤ α`), and then exhibited as *degenerate*, which additionally
needs a nonzero `H¹` class whose cup with everything vanishes.  Estimate: one lane, comparable to
the committed EV-1a/EV-1d pair, since it is the same machinery at a different matrix.

⚠⚠ **THE DIRECTION OF THIS RESIDUAL IS CHALLENGED (wave 69) AND MUST BE SETTLED BEFORE ANY
LANE SPENDS ON IT.**  `Instances/EvenUnramified.lean` argues the opposite: the relator
`x₀^4[x₀,x₁][x₂,x₃]` has the hyperbolic mod-2 cup form, which is *nondegenerate*, so the
reasoning above may be conflating "alternating" with "degenerate"; and `DN 1 0` is a candidate
for `G_{ℚ₂(i)}(2)`, which is Demushkin with `q = 4` rather than not Demushkin.  On that reading
`IsEmpty (NFrame 1 h)` is evidence *for* `q = 4` (the torsion is `ℤ/4`, not `ℤ/2`), which is
what the frame layer requires, rather than evidence against Demushkin-ness.  Neither direction
is proved.  Settle the direction first; if the challenge is right, the lane proves
`IsDemushkin` with `demushkinQ = 4` and this `Prop` is the statement to delete, not to prove. -/
def EvenDemResidualAlphaOneN : Prop := ∀ h : ℕ, ¬ IsDemushkin 2 (DN 1 h : Type)

/-- **Residual R2 (`M` at `α = 1`), DISCHARGED (wave 70)** by
`EvenAlphaOne.evenAlphaOne_residualM`.  The `α = 1` `M` Gram is
`[[1,1,0,0],[1,0,0,0],[0,0,1,1],[0,0,1,0]]`, two copies of the committed head block,
determinant `1`, nondegenerate and not alternating.  There is no asymmetry after all: both
rows are Demushkin at `α = 1`, by the same machinery, exactly as this docstring's last sentence
guessed the machinery would be.  The original text follows.

At `α = 1` the `M` row does not
lose its head diagonal entry; it *gains* a second one at slot `2`, from `c ^ (2 ^ α) = c ²`.  A
Gram with more diagonal entries is not obviously degenerate, so the `M` core may well be
Demushkin at `α = 1` even if R1 holds and the `N` core is not.  `evenDem_demushkinQ_DM_alphaOne`
shows the `M` row still has its `q`-invariant there, which is consistent.  Undecided here.

Cost to close: the `α = 1` `M` Gram, then either its inverse (giving `IsDemushkin` by the §2
dual-vector pattern, unchanged) or a kernel vector.  Estimate: half a lane, and strictly easier
than R1, because the positive direction reuses `evenDualMap` wholesale. -/
def EvenDemResidualAlphaOneM : Prop := ∀ h : ℕ, IsDemushkin 2 (DM 1 h : Type)

/-- **Residual R3 (the rank at `α = 0`).**  The expected *failure* of the recorded
hypothesis-free EV-1b statement on the `N` row.  By `evenDem_nHeadExponent_even_iff` the `α = 0`
relator has odd head exponent, so it survives in the mod-`2` abelianization and should consume
one generator, dropping the rank to `coreRank h - 1`.  This file does not prove that, because the
committed `H¹` computation is unavailable at `α = 0` for exactly that reason.

Cost to close: an `H¹` computation at a relator *outside* the Frattini subgroup, which the
campaign has never needed.  Estimate: one lane, and of no downstream use, since every consumer of
these cores has `2 ≤ α`.  Recorded so that the recorded statement is not retried. -/
def EvenDemResidualAlphaZeroNRank : Prop := ∀ h : ℕ, demushkinRank 2 (DN 0 h : Type) ≠ coreRank h

/-! ## §4 EV-1e final: the assembly endpoints with hypothesis 1 discharged

`evenAssembly_orientedEquivN` / `…M` (`StageAbstractionEvenAssembly.lean:140`, `:160`) carry six
named hypotheses; its module docstring lists hypothesis 1 as
`hmodel : ∀ h, NModelDemushkin α h` (resp. `M`), owned by "a different lane entirely".  That lane
is this one, and its output has been committed since `EvenModelDemushkin.lean` landed, but the
two were never composed: the model files predate the assembly file.  Composing them is the
demonstration that the seam closes.

What remains after this section is five hypotheses, none of them model-side:
`hrec`, `hram`, `hin` (the level-three inputs, including the mod-`8` image seam), `Hrange`
(EV-4a, the cyclotomic image), and `Hres` (the EV-3f residual supply). -/

/-- **EV-1e final, `N` branch.**  Every even-degree dyadic field of degree `2 + 2h` is
`N`-classified, given the five non-model inputs.  This is `evenAssembly_orientedEquivN` with
hypothesis 1 discharged by `evenDem_nModelDemushkin_forall`; `2 ≤ α` is now carried once, by the
endpoint itself, and covers both the Frattini and the Gram thresholds of §3. -/
theorem ev1eFinal_orientedEquivN {α : ℕ} (hα : 2 ≤ α)
    (hrec : EvenLevelThreeRecipSupply) (hram : EvenLevelThreeRamifiedSupply)
    (hin : EvenLevelThreeNFrameInputSupply α)
    (Hrange : ∀ (K : IntermediateField ℚ_[2] ℚ̄₂) [FiniteDimensional ℚ_[2] K]
      [CompactSpace (GalK K)] [T2Space (GalK K)] [TotallyDisconnectedSpace (GalK K)],
      MonoidHom.range (chiCycKTwo (K := K)).toMonoidHom = imChiN α)
    (Hres : ∀ (K : IntermediateField ℚ_[2] ℚ̄₂) [FiniteDimensional ℚ_[2] K]
      [CompactSpace (GalK K)] [T2Space (GalK K)] [TotallyDisconnectedSpace (GalK K)] (h : ℕ),
      EvenClimbResidualSupply (α - 1) (nStageWord α h (Nat.le_of_succ_le hα)) (vN α)
        (maxProPQuotient 2 (GalK K)) (chiCycKTwo (K := K)))
    (K : IntermediateField ℚ_[2] ℚ̄₂) [FiniteDimensional ℚ_[2] K]
    [CompactSpace (GalK K)] [T2Space (GalK K)] [TotallyDisconnectedSpace (GalK K)]
    (h : ℕ) (hev : Module.finrank ℚ_[2] K = 2 + 2 * h) :
    Nonempty (OrientedContinuousMulEquiv (chiN α h) (chiCycKTwo (K := K))) :=
  evenAssembly_orientedEquivN hα (evenDem_nModelDemushkin_forall α hα) hrec hram hin Hrange Hres
    K h hev

/-- **EV-1e final, `M` branch.**  The same composition; the `M` frame input additionally carries
the attained seam. -/
theorem ev1eFinal_orientedEquivM {α : ℕ} (hα : 2 ≤ α)
    (hrec : EvenLevelThreeRecipSupply) (hram : EvenLevelThreeRamifiedSupply)
    (hin : EvenLevelThreeMFrameInputSupply α)
    (Hrange : ∀ (K : IntermediateField ℚ_[2] ℚ̄₂) [FiniteDimensional ℚ_[2] K]
      [CompactSpace (GalK K)] [T2Space (GalK K)] [TotallyDisconnectedSpace (GalK K)],
      MonoidHom.range (chiCycKTwo (K := K)).toMonoidHom = imChiM α)
    (Hres : ∀ (K : IntermediateField ℚ_[2] ℚ̄₂) [FiniteDimensional ℚ_[2] K]
      [CompactSpace (GalK K)] [T2Space (GalK K)] [TotallyDisconnectedSpace (GalK K)] (h : ℕ),
      EvenClimbResidualSupply (α - 1) (mStageWord α h (Nat.le_of_succ_le hα)) (vM α)
        (maxProPQuotient 2 (GalK K)) (chiCycKTwo (K := K)))
    (K : IntermediateField ℚ_[2] ℚ̄₂) [FiniteDimensional ℚ_[2] K]
    [CompactSpace (GalK K)] [T2Space (GalK K)] [TotallyDisconnectedSpace (GalK K)]
    (h : ℕ) (hev : Module.finrank ℚ_[2] K = 2 + 2 * h) :
    Nonempty (OrientedContinuousMulEquiv (chiM α h) (chiCycKTwo (K := K))) :=
  evenAssembly_orientedEquivM hα (evenDem_mModelDemushkin_forall α hα) hrec hram hin Hrange Hres
    K h hev

/-! ## §5 Axiom pins

The §1-§3 declarations are model-side and expected to be std-3 (`propext`, `Classical.choice`,
`Quot.sound`), matching the odd precedent `isDemushkin_DSq`.  The §4 endpoints inherit whatever
the even assembly inherits at its finite-generation station, and are expected to match
`evenAssembly_orientedEquivN` / `…M` exactly, adding nothing: discharging a hypothesis cannot
add axioms beyond those of the proof supplied for it, and that proof is std-3. -/

#print axioms evenDem_isDemushkin_DN
#print axioms evenDem_isDemushkin_DM
#print axioms evenDem_demushkinRank_DN
#print axioms evenDem_demushkinRank_DM
#print axioms evenDem_nModelDemushkin
#print axioms evenDem_mModelDemushkin
#print axioms evenDem_nModelDemushkin_forall
#print axioms evenDem_mModelDemushkin_forall
#print axioms evenDem_nHeadExponent_even_iff
#print axioms evenDem_mHeadExponent_even_iff
#print axioms evenDem_demushkinQ_DM_alphaOne
#print axioms evenDem_nFrame_isEmpty_alphaOne
#print axioms evenDem_nFrame_nonempty_iff
#print axioms ev1eFinal_orientedEquivN
#print axioms ev1eFinal_orientedEquivM

end

end GQ2.Dyadic.EvenDemushkin
