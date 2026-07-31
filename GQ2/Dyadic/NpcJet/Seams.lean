/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Opus-4.8 and Fable-5
-/
import GQ2.Dyadic.NpcJet.Defs
import GQ2.Dyadic.NpcJet.Omega

/-!
# NC lane: the `δ`/`D`/`E` seams of the corrected noncompact-`N` jet

**Ticket NC4** of the NC lane (design memo `docs/dyadic/nc-design.md`, the R3(a) commission).
This file is the memo's `NpcJet/Delta.lean` file-map row (§4.1): the **per-block evaluation
theorems** — the structural-recursion steps that take each factor of the eq:Npc-word to its value
in the Heisenberg slice of the `κ⁰`-extension.  NC5's assembly (`NpcJet/Main.lean`) composes them
into the headline `npc_cross_operators` (memo §2.3) without unfolding anything below.

NC2 (`NpcJet/Defs.lean`) supplies the word, the marking and the slice calculus; NC3
(`NpcJet/Omega.lean`) supplies the two reduction rules and the `η̂`-power vocabulary.  Both are
closed; this file imports them and adds no new definition of its own beyond the seven
`Marking`-level evaluation rewrites of §0.

## The seams, and where the refutation becomes visible

The word is `R_{N,α,r,η} = x₀^{p_α} [x₀, σ^{η̂}] · x₂^{-g} (x₂τ)^{ω₂} · E_{r,η}` with
`E_{r,η} = [D_{r,η}, x₁]`, `D_{r,η} = δ₀^A (δ₀ δ₀^A)^{B⁻¹}` and `δ₀ = (x₀τ)^{ω₂} x₀⁻¹`
(memo §1.1).  At the Gate-E marking each factor evaluates as follows.

| seam | theorem | value |
|---|---|---|
| `δ₀` (memo §3.1) | `npcDeltaW_eval` | `((c₀,1), z_m + q c₀)` |
| `D_{r,η}` (memo §3.2) | `npcDBlock_eval` | `((L_c c₀, 1), ζ_D)`, `ζ_D` quarantined |
| `E_{r,η}` (memo §3.3) | `npcEBlock_eval` | `((0,1), b_q(L_c c₀, c₁))` — **central** |
| `x₂^{-g}` (memo §3.5) | `npcBoundary_invConj_eval` | `1` |
| `(x₂τ)^{ω₂}` (memo §3.5) | `npcBoundary_omega2_eval` | `1` |
| `x₀^{2+2^α}` (memo §3.4) | `npcHeadPow_eval` | `((0,1), q c₀)` |
| `[x₀, σ^{η̂}]` (memo §3.4) | `npcHeadComm_eval` | `(((1+A⁻¹)c₀, 1), q c₀ + Q₀(c₀))` |
| the head, folded | `npcHead_eval` | `(((1+A⁻¹)c₀, 1), Q₀(c₀))` |

Three of these carry the mathematical content of the commission.

* **`δ₀` is where rules 1 and 2 meet.**  Its base `x₀τ` evaluates to the *mixed* element
  `((c₀,u),0)`, the only place the computation leaves the slice.  NC3's
  `nc3_zpowHat_omega2_eq_pow_orderOf` (rule 1, `Odd (orderOf u)`) turns the profinite `ω₂`-power
  into the finite `orderOf u`-th power, and NC2's `elt_pow_eq_sliceElt` fed by NC3's
  `sum_pow_smul_orderOf_eq_zero` (rule 2, `V^u = 0`) collapses that power's `V`-part to `0`.  The
  surviving fibre charge is `powCharge dat u c₀ (orderOf u)` — recorded exactly, never normalized.
* **`D_{r,η}` is where the corrected `L_c` appears.**  Right conjugation applies the *inverse*
  conjugator (NC2's `sliceElt_conj`), so the compressed spelling's two conjugators `â` and `b⁻¹`
  produce the three operators `A⁻¹`, `B`, `B·A⁻¹` — `lcOp_compressed_spelling` is that step, and
  it factors through NC3's `nc3_lcOp_spelling`, whose left-hand side is the *expanded* word's
  three inverse-conjugators.  Draft eq:Ncross's `L_c = A⁻¹` is the first summand alone; the S3.2
  correction is exactly the two summands the draft dropped, and here they are visibly the two
  conjugators of the second `D`-factor.
* **`E_{r,η}` is charge-independent.**  `sliceElt_comm` cancels both arguments' fibres, so
  `npcEBlock_eval` is an *equation*, not an existential: the `D`-block's fibre charge `ζ_D` never
  has to be computed (memo risk 2's quarantine).  This is why the correction contributes exactly
  the missing pairing `b_q(L_c c₀, c₁)` and nothing else.

## What NC5 composes

`npcWord α r η` is the right-nested product `x₀^{p_α} · ([x₀,σ^{η̂}] · (x₂^{-g} · ((x₂τ)^{ω₂} ·
E_{r,η})))`, so the five factor theorems above (or `npcHead_eval` for the first two together) plug
straight into `Marking.eval_mul` and NC2's `sliceElt_mul`.  Every statement is in `sliceElt`-form,
so no raw `Prod` literal is ever exposed (NC2 friction 1) and `CentExt.fib` is read only through
NC2's `sliceElt_fib`.

## Scope notes for NC5/NC6

* **§0 completes `Eval.lean`'s `Marking`-level API.**  `GQ2/Dyadic/Word/Eval.lean` exports
  `Marking.eval_gen/one/mul/inv/sigma2W/deltaW` but not the remaining `PWord` constructors; the
  seven `rfl`-lemmas of §0 fill that gap.  They are stated at full generality (`Marking n G`) and
  belong upstream in `Eval.lean` the moment a second lane wants them — recorded here so that the
  WNP lane does not re-derive them.
* **Hypotheses are per-rule, not bundled.**  `hV2` (char 2), `hu` (`Odd (orderOf u)`, rule 1) and
  `hVu` (`V^u = 0`, rule 2) are threaded individually, and `hα : 2 ≤ α` is consumed only by
  `npcHeadPow_eval`.  Nothing in this file needs `1 ≤ r`, `IsUnit η`, simplicity, faithfulness or
  nonsingularity (memo V3/§2.4).
* No census axiom is cited and none is needed (memo §9); every declaration below is `std-3`.
-/

namespace GQ2.Dyadic

/-! ## §0. `Marking`-level evaluation of the remaining `PWord` constructors

`GQ2/Dyadic/Word/Eval.lean` gives the `Marking`-level rewrites for `gen`, `one`, `mul`, `inv` and
the two derived letters `σ₂`, `δ_i`; the seams below also need `conj`, `comm`, `zpow`, `profPow`
and the three sugar nodes.  All seven are definitional — `Marking.eval` *is* `PWord.eval` at the
coerced marking — and are named exactly as their `PWord.eval` counterparts, so that the memo
§5.3(3) mandate ("no `show`-style definitional steps in the lane") is met at the marking level
too. -/

section MarkingEval

variable {n : ℕ} {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [TotallyDisconnectedSpace G] (t : Marking n G)

/-- `u^g` evaluates to the right conjugate `g⁻¹ (eval u) g`. -/
theorem Marking.eval_conj (u g : PWord (Generator n)) :
    t.eval (.conj u g) = conjR (t.eval u) (t.eval g) := rfl

/-- `[u,v]` evaluates to the paper's commutator `u⁻¹v⁻¹uv`. -/
theorem Marking.eval_comm (u v : PWord (Generator n)) :
    t.eval (.comm u v) = commR (t.eval u) (t.eval v) := rfl

/-- `u^k` (`k : ℤ`) evaluates to the `zpow`. -/
theorem Marking.eval_zpow (u : PWord (Generator n)) (k : ℤ) :
    t.eval (.zpow u k) = t.eval u ^ k := rfl

/-- `u^γ` (`γ ∈ ℤ̂`) evaluates to the profinite power. -/
theorem Marking.eval_profPow (u : PWord (Generator n)) (γ : Zhat) :
    t.eval (.profPow u γ) = t.eval u ^ᶻ γ := rfl

/-- `u^{η̂}` evaluates to the `η̂`-power (memo V4's vehicle). -/
theorem Marking.eval_etaPow (u : PWord (Generator n)) (η : ℤ_[2]) :
    t.eval (u.etaPow η) = t.eval u ^ᶻ etaHatZ η := rfl

/-- `u^{ω₂}` evaluates to the `ω₂`-power. -/
theorem Marking.eval_omega2Pow (u : PWord (Generator n)) :
    t.eval u.omega2Pow = t.eval u ^ᶻ omega2 := rfl

/-- `u^{-g}` is sugar for `(u⁻¹)^g` (packet Rem. 2.3, memo §1.1). -/
theorem Marking.eval_invConj (u g : PWord (Generator n)) :
    t.eval (PWord.invConj u g) = conjR (t.eval u)⁻¹ (t.eval g) := rfl

end MarkingEval

namespace NpcJet

open WordCoh2 SectionEight.AffineTLift QuadraticFp2

section Module

variable {C V : Type} [Group C] [AddCommGroup V] [DistribMulAction C V]
  {q : V → ZMod 2} (dat : FactorSet C V) (hdat : IsEquivariantFactorSet q dat)

/-! ## §1. Slice-calculus completions

Four rewrites NC2's kit does not carry, each needed by exactly one seam below: the `C`-line's
compatibility with integer and profinite exponents (the `D`-block's conjugators and the boundary
block), the power law of the *central* slice (`x₀^{p_α}`), and the commutator of a slice element
with a `C`-line element (`[x₀, σ^{η̂}]`, whose second argument is **not** in the slice, so NC2's
`sliceElt_comm` does not apply). -/

/-- The `C`-line is compatible with integer powers: it is a homomorphism (NC3's `nc3CLine`, of
which NC2's `cLine` is the unbundled form).  Used for the `D`-block conjugator `σ^{−2^r}`. -/
theorem cLine_zpow (c : C) (k : ℤ) : cLine dat hdat c ^ k = cLine dat hdat (c ^ k) :=
  (map_zpow (nc3CLine dat hdat) c k).symm

/-- **The central slice's power law**: `((0,1),w)^n = ((0,1), n·w)`.  The slice element with zero
`V`-part is central and the `κ`-correction `f(0,0)` vanishes, so the fibre is `ZMod 2`-linear. -/
theorem sliceElt_zero_pow (w : ZMod 2) (n : ℕ) :
    sliceElt dat hdat 0 w ^ n = sliceElt dat hdat 0 (n • w) := by
  induction n with
  | zero => rw [pow_zero, zero_smul, sliceElt_zero_zero]
  | succ n ih =>
      rw [pow_succ, ih, sliceElt_mul dat hdat, add_zero, hdat.f_zero_left, add_zero, succ_nsmul]

/-- An **odd** power of a central slice element is itself — the `𝔽₂`-coefficient reading of
`sliceElt_zero_pow`.  This is the step that consumes memo §3.4's `α ≥ 2` (through
`sliceElt_pow_head`). -/
theorem sliceElt_zero_pow_odd {n : ℕ} (hn : Odd n) (w : ZMod 2) :
    sliceElt dat hdat 0 w ^ n = sliceElt dat hdat 0 w := by
  obtain ⟨j, rfl⟩ := hn
  rw [sliceElt_zero_pow dat hdat, add_smul, mul_smul, two_smul, CharTwo.add_self_eq_zero, zero_add,
    one_smul]

/-- **The `p_α`-th power of a slice element** (memo §3.4), `p_α = 2 + 2^α` with `α ≥ 2`: the square
is the central element `((0,1), q v)` and the remaining exponent `1 + 2^{α−1}` is **odd**, so the
`q`-charge survives unchanged.

*Hypothesis carried*: `hα : 2 ≤ α`, i.e. `LabuteType.Valid (.N α)`.  At `α = 1` the cofactor
`1 + 2^0 = 2` is even, the charge dies, and the identity fails as stated — matching S3.1's
`α ≥ 2` Hessian finding. -/
theorem sliceElt_pow_head (hV2 : ∀ v : V, v + v = 0) {α : ℕ} (hα : 2 ≤ α) (v : V) (z : ZMod 2) :
    sliceElt dat hdat v z ^ ((2 : ℤ) + 2 ^ α) = sliceElt dat hdat 0 (q v) := by
  obtain ⟨β, rfl⟩ : ∃ β, α = β + 2 := ⟨α - 2, by omega⟩
  have hz : ((2 : ℤ) + 2 ^ (β + 2)) = ((2 * (1 + 2 ^ (β + 1)) : ℕ) : ℤ) := by push_cast; ring
  rw [hz, zpow_natCast, pow_mul, sliceElt_sq dat hdat hV2,
    sliceElt_zero_pow_odd dat hdat ⟨2 ^ β, by rw [pow_succ]; ring⟩]

/-- **The mixed commutator law**: `[((v,1),z), ((0,g),0)] = (((1+g⁻¹)v, 1), q v + f(v,g⁻¹v) +
m_{g⁻¹}(v))`.

NC2's `sliceElt_comm` needs *both* arguments in the Heisenberg slice; the front block's second
argument `σ^{η̂}` lives on the `C`-line instead, so the fibres no longer cancel and the value
carries the `q`-charge of inversion together with the conjugation correction.  Via
`commR_eq_inv_mul_conjR` this is `sliceElt_inv` followed by `sliceElt_conj`. -/
theorem sliceElt_comm_cLine (hV2 : ∀ v : V, v + v = 0) (v : V) (z : ZMod 2) (g : C) :
    commR (sliceElt dat hdat v z) (cLine dat hdat g)
      = sliceElt dat hdat (v + g⁻¹ • v) (q v + (dat.f v (g⁻¹ • v) + dat.m g⁻¹ v)) := by
  rw [commR_eq_inv_mul_conjR, sliceElt_inv dat hdat hV2, sliceElt_conj dat hdat,
    sliceElt_mul dat hdat]
  congr 1
  have key : ∀ a b c d : ZMod 2, a + b + (a + c) + d = b + (d + c) := by decide
  exact key z (q v) (dat.m g⁻¹ v) (dat.f v (g⁻¹ • v))

section Profinite

variable [Finite C] [Finite V] [TopologicalSpace C] [DiscreteTopology C]

/-- The `C`-line is natural for profinite exponentiation (NC3's `nc3CLine_zpowHat`, in NC2's
vocabulary): the `D`-block's `A`-conjugator `σ^{η̂}` is the `C`-line element of `s ^ᶻ η̂`. -/
theorem cLine_zpowHat (c : C) (γ : Zhat) : cLine dat hdat c ^ᶻ γ = cLine dat hdat (c ^ᶻ γ) :=
  nc3CLine_zpowHat dat hdat c γ

/-- **Reduction rule 1 on the `C`-line** (NC3's `nc3CLine_zpowHat_omega2_eq_one`, in NC2's
vocabulary): the `ω₂`-power of a `C`-line element of odd order is trivial.

*Hypothesis carried*: `hu : Odd (orderOf u)` — "tame inertia is pro-odd". -/
theorem cLine_zpowHat_omega2_eq_one {u : C} (hu : Odd (orderOf u)) :
    cLine dat hdat u ^ᶻ omega2 = 1 :=
  nc3CLine_zpowHat_omega2_eq_one dat hdat hu

end Profinite

section Seams

variable [Finite C] [Finite V] [TopologicalSpace C] [DiscreteTopology C] (s u : C) (c₀ c₁ : V)

/-! ## §2. The letters of the Gate-E marking

Five definitional rewrites, so that no seam below ever has to unfold `npcMarking` or
`Marking.ofLetters`.  The boundary letter `x₂` is `1`: it carries no offset (memo §2.4). -/

theorem npcMarking_eval_sigma :
    (npcMarking dat hdat s u c₀ c₁).eval (PWord.gen .sigma) = cLine dat hdat s := rfl

theorem npcMarking_eval_tau :
    (npcMarking dat hdat s u c₀ c₁).eval (PWord.gen .tau) = cLine dat hdat u := rfl

theorem npcMarking_eval_x_zero :
    (npcMarking dat hdat s u c₀ c₁).eval (PWord.gen (.wild 0)) = sliceElt dat hdat c₀ 0 := rfl

theorem npcMarking_eval_x_one :
    (npcMarking dat hdat s u c₀ c₁).eval (PWord.gen (.wild 1)) = sliceElt dat hdat c₁ 0 := rfl

/-- The boundary letter evaluates to the identity (memo §2.4, §3.5). -/
theorem npcMarking_eval_x_two :
    (npcMarking dat hdat s u c₀ c₁).eval (PWord.gen (.wild 2)) = 1 := rfl

/-! ## §3. The `δ`-letter seam  (memo §3.1)

`δ₀ = (x₀τ)^{ω₂} x₀⁻¹` is the only block whose evaluation leaves the Heisenberg slice: its base
`x₀τ` is the mixed element `((c₀,u),0)`.  Both reduction rules are consumed here, and this is the
only seam that needs either.  The `ω₂`-power is `((0,1), z_m)` with
`z_m = powCharge dat u c₀ (orderOf u)`; multiplying by `x₀⁻¹` — whose fibre is the `q`-charge of
inversion — returns to the slice at `V`-part `c₀`. -/

/-- **The `δ₀` seam** (memo §3.1): at the Gate-E marking `δ₀` evaluates to the slice element with
`V`-part `c₀` and fibre `z_m + q c₀`, where `z_m = powCharge dat u c₀ (orderOf u)` is the
accumulated charge of the `orderOf u`-th power of `((c₀,u),0)`.

*Hypotheses carried*: `hV2` (characteristic 2, for the inversion law), `hu : Odd (orderOf u)`
(rule 1) and `hVu : V^u = 0` (rule 2).  Nothing else.

The charge is recorded exactly rather than existentially so that the statement is an equation;
`exists_npcDeltaW_eval` is the quarantined form the `D`-seam actually consumes (memo risk 2). -/
theorem npcDeltaW_eval (hV2 : ∀ v : V, v + v = 0) (hu : Odd (orderOf u))
    (hVu : ∀ v : V, u • v = v → v = 0) :
    (npcMarking dat hdat s u c₀ c₁).eval (deltaW 0)
      = sliceElt dat hdat c₀ (powCharge dat u c₀ (orderOf u) + q c₀) := by
  have hy : (elt dat hdat c₀ u 0).base = Sd.mk c₀ u := rfl
  rw [Marking.eval_deltaW, npcMarking_x_zero, npcMarking_τ, sliceElt_mul_cLine,
    nc3_zpowHat_omega2_eq_pow_orderOf dat hdat hu hVu hy,
    elt_pow_eq_sliceElt dat hdat (pow_orderOf_eq_one u) (sum_pow_smul_orderOf_eq_zero hVu c₀),
    sliceElt_inv dat hdat hV2, sliceElt_mul dat hdat, zero_add, hdat.f_zero_left, add_zero,
    zero_add]

/-- The `δ₀` seam with its fibre charge quarantined (memo risk 2): all the `D`-block needs is that
`δ₀` is *some* slice element with `V`-part `c₀`. -/
theorem exists_npcDeltaW_eval (hV2 : ∀ v : V, v + v = 0) (hu : Odd (orderOf u))
    (hVu : ∀ v : V, u • v = v → v = 0) :
    ∃ γ₀ : ZMod 2, (npcMarking dat hdat s u c₀ c₁).eval (deltaW 0) = sliceElt dat hdat c₀ γ₀ :=
  ⟨_, npcDeltaW_eval dat hdat s u c₀ c₁ hV2 hu hVu⟩

/-! ## §4. The `D`-block seam  (memo §3.2)

`D_{r,η} = δ₀^A (δ₀ δ₀^A)^{B⁻¹}` in the compressed spelling NC2's `npcDBlock` uses.  Right
conjugation applies the **inverse** conjugator (`conjR x g = g⁻¹ x g`, NC2's `sliceElt_conj`), so
the two conjugator nodes `â = σ^{η̂}` and `σ^{−2^r}` contribute the three operators

```
A⁻¹  (from δ₀^â),        B  (from (δ₀ ⋯)^{σ^{−2^r}}),        B·A⁻¹  (from (δ₀^â)^{σ^{−2^r}})
```

— the corrected `L_c = A⁻¹ + B + B·A⁻¹`.  The draft's `L_c = A⁻¹` is the first summand alone. -/

/-- **`L_c` from the compressed spelling** (memo §3.2): the `V`-part the `D`-block's two
conjugations produce *is* `lcOp`.

The left-hand side is what the compressed `D`-block literally evaluates to — the first conjugator
`â` applied to `δ₀`, then the second conjugator `σ^{−2^r}` applied to `δ₀ · δ₀^{â}`.  Distributing
the second conjugator over that sum splits its contribution into the operators `B` and `B·A⁻¹`,
and the resulting three-term sum is NC3's `nc3_lcOp_spelling` — whose own left-hand side is the
*expanded* word's three inverse-conjugators `A⁻¹`, `B`, `(A·B⁻¹)⁻¹`.  Compressed and expanded
spellings therefore agree operator by operator, which is the memo's "`L_c` is literally the sum of
the three inverse-conjugators" reading. -/
theorem lcOp_compressed_spelling (η : ℤ_[2]) (r : ℕ) (v : V) :
    (s ^ᶻ etaHatZ η)⁻¹ • v + (s ^ (-(2 ^ r : ℤ)))⁻¹ • (v + (s ^ᶻ etaHatZ η)⁻¹ • v)
      = lcOp s η r v := by
  rw [smul_add, ← add_assoc, ← mul_smul, ← mul_inv_rev]
  exact nc3_lcOp_spelling s η r v

/-- **The `D`-block seam, structural form** (memo §3.2): given *any* slice value of `δ₀` with
`V`-part `c₀`, the `D`-block evaluates to a slice element with `V`-part `L_c c₀`.

Taking the `δ₀` charge as a hypothesis and returning the `D` charge existentially is memo risk 2's
quarantine, made structural: the three γ's, the `m`-corrections and the one `f`-cross-term that
make up `ζ_D` are never assembled, because `npcEBlock_eval` cancels them. -/
theorem npcDBlock_eval_of_deltaW (η : ℤ_[2]) (r : ℕ) {γ₀ : ZMod 2}
    (hδ : (npcMarking dat hdat s u c₀ c₁).eval (deltaW 0) = sliceElt dat hdat c₀ γ₀) :
    ∃ ζ : ZMod 2, (npcMarking dat hdat s u c₀ c₁).eval (npcDBlock η r)
      = sliceElt dat hdat (lcOp s η r c₀) ζ := by
  rw [npcDBlock, Marking.eval_mul, Marking.eval_conj, Marking.eval_conj, Marking.eval_mul,
    Marking.eval_conj, Marking.eval_etaPow, Marking.eval_zpow,
    npcMarking_eval_sigma dat hdat s u c₀ c₁, hδ, cLine_zpowHat dat hdat, cLine_zpow dat hdat,
    sliceElt_conj dat hdat, sliceElt_mul dat hdat, sliceElt_conj dat hdat, sliceElt_mul dat hdat]
  exact ⟨_, by rw [lcOp_compressed_spelling s η r c₀]⟩

/-- **The `D`-block seam** (memo §3.2): at the Gate-E marking `D_{r,η}` evaluates to a slice
element with `V`-part `L_c c₀`, `L_c = A⁻¹ + B + B·A⁻¹` the S3.2-corrected cross operator.

*Hypotheses carried*: `hV2`, `hu` and `hVu`, all three inherited from the `δ₀` seam; the `D`-block
itself needs no hypothesis at all beyond `δ₀`'s value. -/
theorem npcDBlock_eval (hV2 : ∀ v : V, v + v = 0) (hu : Odd (orderOf u))
    (hVu : ∀ v : V, u • v = v → v = 0) (η : ℤ_[2]) (r : ℕ) :
    ∃ ζ : ZMod 2, (npcMarking dat hdat s u c₀ c₁).eval (npcDBlock η r)
      = sliceElt dat hdat (lcOp s η r c₀) ζ :=
  npcDBlock_eval_of_deltaW dat hdat s u c₀ c₁ η r (npcDeltaW_eval dat hdat s u c₀ c₁ hV2 hu hVu)

/-! ## §5. The `E`-block seam  (memo §3.3)

`E_{r,η} = [D_{r,η}, x₁]`.  Both arguments are in the Heisenberg slice, so NC2's `sliceElt_comm`
applies: the value is **central**, with `V`-part `0` and fibre exactly the polar pairing.  Both
fibres cancel — the `D`-block's charge `ζ_D` and the `x₁`-letter's `0` — so the seam is an
equation with no residual quantifier.  This is the point at which the refutation of draft
eq:Ncross becomes visible in the answer and not merely in the computation's shape: the cross term
is `b_q(L_c c₀, c₁)` with the corrected three-summand `L_c`. -/

/-- **The `E`-block seam** (memo §3.3): the correction block evaluates to the central element
`((0,1), b_q(L_c c₀, c₁))`.

*Hypotheses carried*: `hV2`, `hu`, `hVu` — all three only through the `D`-block's `V`-part.  The
commutator step itself is charge-independent, which is why this is an equation.  `polar` is
symmetric, so the fibre *is* the pairing `b_q(c₁, L_c c₀)` of the headline statement. -/
theorem npcEBlock_eval (hV2 : ∀ v : V, v + v = 0) (hu : Odd (orderOf u))
    (hVu : ∀ v : V, u • v = v → v = 0) (η : ℤ_[2]) (r : ℕ) :
    (npcMarking dat hdat s u c₀ c₁).eval (npcEBlock η r)
      = sliceElt dat hdat 0 (polar q (lcOp s η r c₀) c₁) := by
  obtain ⟨ζ, hζ⟩ := npcDBlock_eval dat hdat s u c₀ c₁ hV2 hu hVu η r
  rw [npcEBlock, Marking.eval_comm, hζ, npcMarking_eval_x_one dat hdat s u c₀ c₁,
    sliceElt_comm dat hdat hV2]

/-! ## §6. The boundary block  (memo §3.5)

`x₂^{-g} (x₂τ)^{ω₂}` with `g = x₁σ^{2^r}`.  The boundary letter carries lower value `1` and no
offset, so the conjugated factor is trivial *whatever* `g` is, and the tame factor dies by rule 1.
No second-order residue survives — consistent with the boundary column of the noncompact wild row
being Gate-D (first-order) data only. -/

/-- **The conjugated boundary factor dies** (memo §3.5): `x₂^{-g} = 1` for every `g`, because the
boundary letter itself evaluates to `1`.  Stated for an arbitrary conjugator so that NC5 need not
evaluate `g = x₁σ^{2^r}` at all. -/
theorem npcBoundary_invConj_eval (g : PWord (Generator 2)) :
    (npcMarking dat hdat s u c₀ c₁).eval (PWord.invConj (.gen (.wild 2)) g) = 1 := by
  rw [Marking.eval_invConj, npcMarking_eval_x_two dat hdat s u c₀ c₁, inv_one, one_conjR]

/-- **The tame boundary factor dies exactly** (memo §3.5): `(x₂τ)^{ω₂} = 1`, by reduction rule 1
on the `C`-line.

*Hypothesis carried*: `hu : Odd (orderOf u)`, rule 1's.  Without it the `ω₂`-power is the
`2`-primary part of the `τ`-image and the boundary block leaves a residue. -/
theorem npcBoundary_omega2_eval (hu : Odd (orderOf u)) :
    (npcMarking dat hdat s u c₀ c₁).eval
        (PWord.omega2Pow (.mul (.gen (.wild 2)) (.gen .tau))) = 1 := by
  rw [Marking.eval_omega2Pow, Marking.eval_mul, npcMarking_eval_x_two dat hdat s u c₀ c₁,
    npcMarking_eval_tau dat hdat s u c₀ c₁, one_mul, cLine_zpowHat_omega2_eq_one dat hdat hu]

/-! ## §7. The linear head  (memo §3.4)

`x₀^{p_α} [x₀, σ^{η̂}]`, `p_α = 2 + 2^α`.  Both factors are central-slice computations; their two
`q(c₀)`-charges cancel in characteristic 2, and what survives is exactly `npcQ0` — the
`PLUS_FORM_TEXT_NONCOMPACT` display `β_A(a, A⁻¹a) + c_{A⁻¹}(a)`, with the twisted-lift term
landing as the factor-set correction `dat.m`. -/

/-- **The `p_α`-power factor** (memo §3.4): `x₀^{2+2^α}` evaluates to the central element
`((0,1), q c₀)`.

*Hypotheses carried*: `hV2` and `hα : 2 ≤ α` (`LabuteType.Valid (.N α)`) — the sole consumer of
`hα` in the lane. -/
theorem npcHeadPow_eval (hV2 : ∀ v : V, v + v = 0) {α : ℕ} (hα : 2 ≤ α) :
    (npcMarking dat hdat s u c₀ c₁).eval (.zpow (.gen (.wild 0)) ((2 : ℤ) + 2 ^ α))
      = sliceElt dat hdat 0 (q c₀) := by
  rw [Marking.eval_zpow, npcMarking_eval_x_zero dat hdat s u c₀ c₁, sliceElt_pow_head dat hdat hV2 hα]

/-- **The commutator factor of the head** (memo §3.4): `[x₀, σ^{η̂}]` evaluates to
`(((1+A⁻¹)c₀, 1), q c₀ + Q₀(c₀))`.

The second argument lives on the `C`-line, not in the slice, so this is `sliceElt_comm_cLine`
rather than NC2's `sliceElt_comm`; the surviving `q(c₀)` is what the `p_α`-factor cancels.

*Hypothesis carried*: `hV2` only. -/
theorem npcHeadComm_eval (hV2 : ∀ v : V, v + v = 0) (η : ℤ_[2]) :
    (npcMarking dat hdat s u c₀ c₁).eval (.comm (.gen (.wild 0)) ((PWord.gen .sigma).etaPow η))
      = sliceElt dat hdat (c₀ + (s ^ᶻ etaHatZ η)⁻¹ • c₀) (q c₀ + npcQ0 dat s η c₀) := by
  rw [Marking.eval_comm, npcMarking_eval_x_zero dat hdat s u c₀ c₁, Marking.eval_etaPow,
    npcMarking_eval_sigma dat hdat s u c₀ c₁, cLine_zpowHat dat hdat,
    sliceElt_comm_cLine dat hdat hV2]
  rfl

/-- **The head, folded** (memo §3.4): the product `x₀^{p_α} [x₀, σ^{η̂}]` evaluates to
`(((1+A⁻¹)c₀, 1), Q₀(c₀))` — the two `q(c₀)`-charges cancel in characteristic 2, leaving the
diagonal part free of a diagonal `q`-term, which is exactly what `npcQ0` records.

Supplied for readability; `npcWord` is right-nested, so NC5 may equally compose the two factor
lemmas directly through `Marking.eval_mul`. -/
theorem npcHead_eval (hV2 : ∀ v : V, v + v = 0) {α : ℕ} (hα : 2 ≤ α) (η : ℤ_[2]) :
    (npcMarking dat hdat s u c₀ c₁).eval
        (.mul (.zpow (.gen (.wild 0)) ((2 : ℤ) + 2 ^ α))
          (.comm (.gen (.wild 0)) ((PWord.gen .sigma).etaPow η)))
      = sliceElt dat hdat (c₀ + (s ^ᶻ etaHatZ η)⁻¹ • c₀) (npcQ0 dat s η c₀) := by
  rw [Marking.eval_mul, npcHeadPow_eval dat hdat s u c₀ c₁ hV2 hα,
    npcHeadComm_eval dat hdat s u c₀ c₁ hV2 η, sliceElt_mul dat hdat, zero_add,
    hdat.f_zero_left, add_zero]
  congr 1
  have key : ∀ a b : ZMod 2, a + (a + b) = b := by decide
  exact key (q c₀) (npcQ0 dat s η c₀)

end Seams

end Module

end NpcJet

end GQ2.Dyadic
