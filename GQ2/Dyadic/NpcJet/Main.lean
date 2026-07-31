/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Opus-4.8 and Fable-5
-/
import GQ2.Dyadic.NpcJet.Seams

/-!
# The corrected noncompact-`N` cross-operator theorem

**Ticket NC5** of the NC lane — the headline of the R3(a) commission (design memo
`docs/dyadic/nc-design.md` §2.3, §2.4).  This file is the memo's `NpcJet/Main.lean` file-map row
(§4.1): the `h = 0` assembly of NC4's five block-evaluation seams into

```
fib (eval R_{N,α,r,η}) = Q₀(c₀) + b_q(c₁, L_c c₀),      L_c = A⁻¹ + B + B·A⁻¹
```

— `npc_cross_operators` — together with the packet-facing companion `hVu_of_simple` and a
concrete `(α, r, η)` stress pin.

## Contents

* **§1 the headline** — `npc_cross_operators` (memo §2.3), in the hypothesis-minimal form of
  memo §2.4.
* **§2 the companion** — `hVu_of_simple`, the bridge from the packet's ramified-simple bundle to
  the headline's `hVu`, and `npc_cross_operators_of_simple`, the headline repackaged over that
  bundle.
* **§3 stress tests** — the discrepancy display `lcOp_eq_draft_add_discrepancy` and its
  degeneration `lcOp_eq_draft_of_eq_one` (errata item 5 in two lines), and the headline pinned at
  `(α, r, η) = (2, 1, 1)`.

## What the theorem says, and why it exists

The draft's display eq:Ncross claims `L_c = A⁻¹` (and `M_c = A`) for the second jet of the
noncompact `N_α` relator on ramified simples.  The simplification campaign's engine
**machine-refuted** that display at S3.2 (`general_2adic` `N.py` `CROSS_OPERATOR_FINDING`;
campaign `BOARD.md` S3.2 row): reducing the universal twisted class-two value of the eq:Npc-word
by the three ramified reduction rules gives the strictly larger operator

```
L_c = A⁻¹ + B + B·A⁻¹ = 1 + (1 + A⁻¹)(1 + B),     M_c = adj(L_c) = A + B⁻¹ + A·B⁻¹,
A = σ^{η̂},   B = σ^{2^r}
```

validated at six instances on both twisted ramified simples.  The discrepancy `B(1 + A⁻¹)`
vanishes exactly when `A = 1`, so the draft's display is the first summand alone.  This is
**errata item 5** of the campaign's errata bundle (`docs/dyadic/packet-errata-draft.md`), and the
owner's R3 decision (option (a)) was to prove the corrected identity in Lean rather than leave the
twisted path at diagnostic status.  `npc_cross_operators` is that proof.

The refutation is visible in the *shape* of the proof, not only in its answer: right conjugation
applies the inverse conjugator (`conjR x g = g⁻¹ x g`, NC2's `sliceElt_conj`), so the `D`-block's
two conjugator nodes `â = σ^{η̂}` and `σ^{−2^r}` contribute the three operators `A⁻¹`, `B`,
`B·A⁻¹` — literally the sum of the three inverse-conjugators (NC4's `lcOp_compressed_spelling`,
memo §3.2).  A reader can see which two summands the draft dropped.

## `M_c` needs no Lean object

`polar` is symmetric (`QuadraticFp2.polar_comm`), so `polar q c₁ (lcOp s η r c₀)` **is** the
pairing `b_q(c₁, L_c c₀)`, and the adjoint `M_c = adj(L_c) = A + B⁻¹ + A·B⁻¹` is the same datum
read in the other slot of the symmetric pairing.  Per the memo's owner Q6 (docstring reading
adopted), no second definition and no `npc_cross_operators_adjoint` corollary is introduced: an
object with no Lean consumer would only have to be maintained.

## How it is assembled

`npcWord α r η` is the right-nested product

```
x₀^{2+2^α} · ([x₀, σ^{η̂}] · (x₂^{-g} · ((x₂τ)^{ω₂} · E_{r,η}))),      g = x₁σ^{2^r}
```

so the proof is four `Marking.eval_mul`s, NC4's five factor theorems (`npcHeadPow_eval`,
`npcHeadComm_eval`, `npcBoundary_invConj_eval`, `npcBoundary_omega2_eval`, `npcEBlock_eval`), the
two `one_mul`s the dead boundary block leaves behind, two `sliceElt_mul`s, and the `𝔽₂`
cancellation `a + (a + b + c + 0) + 0 = b + c` by kernel `decide`.  Nothing below the seams is
unfolded: the `δ₀` charge `z_m` and the `D`-block charge `ζ_D` are never assembled (memo risk 2's
quarantine — `npcEBlock_eval` is charge-independent), and no raw `Prod` literal is ever exposed
(NC2 friction 1).  The two `q(c₀)`-charges of the head cancel inside `npcHead_eval`; the one that
survives to this file is the head's own, cancelled here against `npcHeadComm_eval`'s.

## Hypothesis surface (memo §2.4, the hypothesis-minimal form)

Only four mathematical hypotheses, each traceable to one reduction rule or one block:

| hypothesis | consumed by | rule |
|---|---|---|
| `hV2 : ∀ v, v + v = 0` | the slice calculus throughout | characteristic 2 |
| `hu : Odd (orderOf u)` | `δ₀` and the tame boundary factor | rule 1, `tame-omega2-power` |
| `hVu : ∀ v, u • v = v → v = 0` | `δ₀` only | rule 2, `tame-geom-vanishes` |
| `hα : 2 ≤ α` | `x₀^{2+2^α}` only | `LabuteType.Valid (.N α)` |

`hα` is sharp: at `α = 1` the cofactor `1 + 2^0 = 2` is even, the `q(c₀)`-charge dies, and the
identity fails as stated — matching S3.1's `α ≥ 2` Hessian finding.

Everything else is *absent by design*.  In particular the theorem quantifies over **all** `r : ℕ`
and **all** `η : ℤ_[2]`: neither `1 ≤ r` nor `IsUnit η` is consumed anywhere, so the
draft-validity side conditions stay on the word row where they belong, and the statement is
strictly stronger than the commissioned "for all `r ≥ 1`, `η ∈ ℤ₂ˣ`".  (`η` quantifies over the
`η̂`-*value*, which also subsumes the Python engine's pinned-`EtaHat`-instances limitation —
`N.py` `check_eta`, "eta cannot be symbolic".)  Simplicity, faithfulness, nonsingularity,
invariance of `q` and the tame relation `sus⁻¹ = u^{q_K}` are likewise not needed; `hVu_of_simple`
below recovers `hVu` from the packet's ramified-simple bundle for consumers who want to
instantiate there.

The instance surface is `[Finite C] [Finite V]` plus `[TopologicalSpace C] [DiscreteTopology C]`
(the evaluator's five typeclasses on `CentExt (kappa0Cocycle dat hdat)` synthesize from finite +
discrete, memo §5.2).  The memo §2.3 display also carried `[TopologicalSpace V]
[DiscreteTopology V]`; they are not used and are omitted — the only deviation from the verbatim
display, and one in the hypothesis-minimal direction.

## Scope, and what consumes this

Out of scope **deliberately** (memo risk 5): the three-variable Gate-D diagnostic form (an offset
on the boundary letter `x₂`, which the Gate-E marking deliberately omits), and invertibility of
`L_c` per module class.  Invertibility genuinely varies with the module and belongs with WNP-c's
Fox/normal-form clauses; anyone citing this theorem for "the `c₀`–`c₁` pairing is restored" still
owes that, and on a concrete battery module it is a `decide`.

* **WNP-c** (packet row WC-Npc, Def. 9.1 item (6)) cites `npc_cross_operators` instead of
  re-deriving the identity: it is exactly the "claimed cross operators for all allowed `r, η`"
  the row asks for, with "claimed" now meaning the S3.2-corrected operators.
* **NC6** owes the handle tail `H_h` (memo §2.5: the conclusion gains
  `∑ j, b_q(e_{2j}, e_{2j+1})`, an induction on `h` independent of this core) and, if wanted, a
  fully concrete module instantiation of the stress pin of §3 (a `FactorSet` on a small
  fixed-point-free `C`-module — the pin here is at concrete `(α, r, η)`, over an arbitrary
  module).
* No census axiom is cited and none is needed (memo §9).  Measured on the built module:
  `#print axioms GQ2.Dyadic.NpcJet.npc_cross_operators` prints
  `[propext, Classical.choice, Quot.sound]` — std-3.  Every declaration in this file prints
  std-3 or a subset of it (`hVu_of_simple` prints `[propext, Quot.sound]`).
-/

namespace GQ2.Dyadic.NpcJet

open WordCoh2 SectionEight.AffineTLift QuadraticFp2

section Module

variable {C V : Type} [Group C] [AddCommGroup V] [DistribMulAction C V]
  {q : V → ZMod 2} (dat : FactorSet C V) (hdat : IsEquivariantFactorSet q dat)

/-! ## §1. The headline (memo §2.3) -/

section Headline

variable [Finite C] [Finite V] [TopologicalSpace C] [DiscreteTopology C]

/-- **The corrected noncompact-`N` cross-operator identity** (S3.2 finding, R3(a) commission;
replaces draft display eq:Ncross, errata item 5).

On any `𝔽₂`-module of a finite group in which the `τ`-image `u` has odd order and no nonzero
fixed vector, the second jet of the noncompact relator `R_{N,α,r,η}` at the Gate-E marking is

```
Q(c₀, c₁) = Q₀(c₀) + b_q(c₁, L_c c₀),        L_c = A⁻¹ + B + B·A⁻¹,
A = σ^{η̂},  B = σ^{2^r}
```

— symbolically in `r` and `η`, i.e. for **all** `r : ℕ` and **all** `η : ℤ_[2]` (memo §2.4: no
`1 ≤ r`, no `IsUnit η`; the draft-validity side conditions live on the word row).  The draft's
`L_c = A⁻¹` is the first summand of `lcOp` alone.

The diagonal part `npcQ0 c₀ = β_A(c₀, A⁻¹c₀) + c_{A⁻¹}(c₀)` carries no diagonal `q`-term: the
`q(c₀)` of `x₀^{2+2^α}` cancels against the one from `[x₀, σ^{η̂}]`, which is exactly what `hα`
buys.  `polar` is symmetric, so the cross term is `b_q(c₁, L_c c₀)` and the adjoint
`M_c = A + B⁻¹ + A·B⁻¹` is the same datum read in the other slot (module docstring).

*Hypotheses*: `hV2` (characteristic 2), `hu` (rule 1), `hVu` (rule 2), `hα` (`α ≥ 2`, sharp).
Nothing else — see `hVu_of_simple` for the bridge to the packet's ramified-simple bundle. -/
theorem npc_cross_operators (hV2 : ∀ v : V, v + v = 0)
    (s u : C) (hu : Odd (orderOf u)) (hVu : ∀ v : V, u • v = v → v = 0)
    (α : ℕ) (hα : 2 ≤ α) (r : ℕ) (η : ℤ_[2]) (c₀ c₁ : V) :
    ((npcMarking dat hdat s u c₀ c₁).eval (npcWord α r η)).fib
      = npcQ0 dat s η c₀ + polar q c₁ (lcOp s η r c₀) := by
  rw [npcWord, Marking.eval_mul, Marking.eval_mul, Marking.eval_mul, Marking.eval_mul,
    npcHeadPow_eval dat hdat s u c₀ c₁ hV2 hα,
    npcHeadComm_eval dat hdat s u c₀ c₁ hV2 η,
    npcBoundary_invConj_eval dat hdat s u c₀ c₁ _,
    npcBoundary_omega2_eval dat hdat s u c₀ c₁ hu,
    npcEBlock_eval dat hdat s u c₀ c₁ hV2 hu hVu η r,
    one_mul, one_mul, sliceElt_mul dat hdat, sliceElt_mul dat hdat, sliceElt_fib,
    hdat.f_zero_right, hdat.f_zero_left, polar_comm]
  -- Pure `𝔽₂` bookkeeping: the head's two `q(c₀)`-charges cancel and the two vanishing
  -- `κ`-cross-terms (`f(v,0)`, `f(0,w)`) drop out.
  have key : ∀ a b c : ZMod 2, a + (a + b + c + 0) + 0 = b + c := by decide
  exact key (q c₀) (npcQ0 dat s η c₀) (polar q c₁ (lcOp s η r c₀))

end Headline

/-! ## §2. The packet-facing companion (memo §2.4)

The headline's `hVu` is rule 2's hypothesis, `V^u = 0`, stated directly.  The packet phrases the
same condition as "on every ramified simple", and the repo's canonical spelling of that bundle is
`DetRamified.prop_6_18_ramified`'s `hsimple`/`hram` pair.  `hVu_of_simple` is the bridge: for a
`u` whose powers are normal in `C`, the fixed submodule `V^u` is a `C`-submodule, so simplicity
forces it to be `⊥` or `⊤` — and ramification rules out `⊤`.

The normality hypothesis is genuinely needed and genuinely available: `V^u` is only `C`-stable
when conjugates of `u` act on `V^u` trivially, and in the intended application `C = ⟨s, u⟩` with
the oriented tame relation `s u s⁻¹ = u^{q_K}`, which puts every conjugate of `u` in
`Subgroup.zpowers u`.  It is stated as the plain `∀ g, g * u * g⁻¹ ∈ Subgroup.zpowers u` rather
than as `(Subgroup.zpowers u).Normal` so that a consumer holding only the tame relation can
discharge it without instance plumbing (`Subgroup.Normal.conj_mem` supplies it in one step from
the class form). -/

section Companion

/-- **The ramified-simple bridge** (memo §2.4): on a simple `C`-module on which `u` acts
nontrivially and whose powers are normal in `C`, the fixed submodule `V^u` vanishes — which is
exactly the headline's `hVu`.

The proof is the memo's: `V^u` is `C`-stable because for `h : C` the normality hypothesis writes
`h⁻¹ u h = u^k`, and `u^k` fixes whatever `u` fixes (the stabilizer is a subgroup, closed under
`zpow`); `hsimple` then leaves `⊥` or `⊤`, and `hram` kills `⊤`.

No semisimplicity, no character theory, and no hypothesis on `q`, `dat` or the topology: this is
a statement about the `C`-module `V` alone.  Consumers holding the `prop_6_18_ramified` bundle
(`hsimple`, `hram : ∃ v, c tameTau • v ≠ v`) instantiate at `u := c tameTau`. -/
theorem hVu_of_simple {u : C}
    (hsimple : ∀ W : AddSubgroup V, (∀ h : C, ∀ w ∈ W, h • w ∈ W) → W = ⊥ ∨ W = ⊤)
    (hram : ∃ v : V, u • v ≠ v) (hnorm : ∀ g : C, g * u * g⁻¹ ∈ Subgroup.zpowers u) :
    ∀ v : V, u • v = v → v = 0 := by
  -- `W = V^u`, the fixed submodule.
  set W : AddSubgroup V :=
    { carrier := {v : V | u • v = v}
      add_mem' := fun {a b} ha hb => show u • (a + b) = a + b by rw [smul_add, ha, hb]
      zero_mem' := smul_zero u
      neg_mem' := fun {a} ha => show u • (-a) = -a by rw [smul_neg, ha] } with hW
  have hmem : ∀ v : V, v ∈ W ↔ u • v = v := fun _ => Iff.rfl
  -- `W` is `C`-stable: `h⁻¹ u h = u ^ k`, and `u ^ k` fixes every `u`-fixed vector.
  have hstable : ∀ h : C, ∀ w ∈ W, h • w ∈ W := by
    intro h w hw
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (hnorm h⁻¹)
    have hfix : u ^ k • w = w := zpow_mem (show u ∈ MulAction.stabilizer C w from hw) k
    have hconj : u * h = h * u ^ k := by
      rw [hk, inv_inv]
      group
    exact (hmem _).mpr <| by rw [smul_smul, hconj, mul_smul, hfix]
  -- Simplicity leaves `⊥` or `⊤`; ramification rules out `⊤`.
  rcases hsimple W hstable with hbot | htop
  · exact fun v hv => AddSubgroup.mem_bot.mp (hbot ▸ (hmem v).mpr hv)
  · obtain ⟨v, hv⟩ := hram
    exact absurd ((hmem v).mp (htop ▸ AddSubgroup.mem_top v)) hv

end Companion

section Instantiation

variable [Finite C] [Finite V] [TopologicalSpace C] [DiscreteTopology C]

/-- **The headline at the packet's module class** (memo §2.4): `npc_cross_operators` with `hVu`
discharged by `hVu_of_simple`, so that a consumer holding the `prop_6_18_ramified` bundle
(`hsimple`, `hram`) plus the tame normality can cite the identity directly.

Note what is *still* absent even in this packaging: faithfulness, nonsingularity of `q`,
invariance of `q`, `1 ≤ r` and `IsUnit η`.  The jet identity does not see them. -/
theorem npc_cross_operators_of_simple (hV2 : ∀ v : V, v + v = 0) (s u : C) (hu : Odd (orderOf u))
    (hsimple : ∀ W : AddSubgroup V, (∀ h : C, ∀ w ∈ W, h • w ∈ W) → W = ⊥ ∨ W = ⊤)
    (hram : ∃ v : V, u • v ≠ v) (hnorm : ∀ g : C, g * u * g⁻¹ ∈ Subgroup.zpowers u)
    (α : ℕ) (hα : 2 ≤ α) (r : ℕ) (η : ℤ_[2]) (c₀ c₁ : V) :
    ((npcMarking dat hdat s u c₀ c₁).eval (npcWord α r η)).fib
      = npcQ0 dat s η c₀ + polar q c₁ (lcOp s η r c₀) :=
  npc_cross_operators dat hdat hV2 s u hu (hVu_of_simple hsimple hram hnorm) α hα r η c₀ c₁

end Instantiation

/-! ## §3. Stress tests

The repo idiom: pin the general statement at concrete data and check that the specialization is
the expected display.  Two pins here — the headline at the packet's procyclic row, and the
corrected operator against the refuted draft display. -/

section StressTests

variable [Finite C] [TopologicalSpace C] [DiscreteTopology C]

/-- **The discrepancy display** (memo §1.2): `L_c` is the draft's `A⁻¹` plus `B·(1 + A⁻¹)`.  This
is the errata item 5 claim in one line — the draft kept the first summand and dropped the
factored remainder. -/
theorem lcOp_eq_draft_add_discrepancy (s : C) (η : ℤ_[2]) (r : ℕ) (v : V) :
    lcOp s η r v = (s ^ᶻ etaHatZ η)⁻¹ • v + s ^ (2 ^ r) • (v + (s ^ᶻ etaHatZ η)⁻¹ • v) := by
  rw [lcOp, smul_add, ← mul_smul, add_assoc]

/-- **The discrepancy vanishes at `A = 1`** (memo §1.2: "the discrepancy `B(1 + A⁻¹)` vanishes iff
`A = 1`"): there, and only in char 2 for free, the corrected `L_c` agrees with the draft's `A⁻¹`.
Away from `A = 1` the two operators differ, which is what the six-instance battery detected. -/
theorem lcOp_eq_draft_of_eq_one (hV2 : ∀ v : V, v + v = 0) (s : C) (η : ℤ_[2]) (r : ℕ)
    (hA : s ^ᶻ etaHatZ η = 1) (v : V) : lcOp s η r v = (s ^ᶻ etaHatZ η)⁻¹ • v := by
  rw [lcOp_eq_draft_add_discrepancy, hA, inv_one, one_smul, hV2, smul_zero, add_zero]

/-- The pinned cross operator in closed form: at `r = 1` the `B`-element is `s²`, so the pin's
`L_c` is `A⁻¹ + s² + s²A⁻¹` with `A = s ^ᶻ η̂(1)`. -/
theorem lcOp_pin (s : C) (η : ℤ_[2]) (v : V) :
    lcOp s η 1 v = (s ^ᶻ etaHatZ η)⁻¹ • v + s ^ 2 • v + (s ^ 2 * (s ^ᶻ etaHatZ η)⁻¹) • v := by
  rw [lcOp, pow_one]

variable [Finite V]

/-- **The headline pinned at `(α, r, η) = (2, 1, 1)`** — the smallest valid Labute exponent
(`hα` discharged by `le_rfl`) together with the procyclic row `(r, ε, η) = (1, 1, 1)` that the
campaign's `ℚ₂(√-10)` instance uses (dyadic merge gate 9).  The `2 ≤ α` side condition is the only
one there is, so the pin needs no arithmetic side goal. -/
theorem npc_cross_operators_pin (hV2 : ∀ v : V, v + v = 0)
    (s u : C) (hu : Odd (orderOf u)) (hVu : ∀ v : V, u • v = v → v = 0) (c₀ c₁ : V) :
    ((npcMarking dat hdat s u c₀ c₁).eval (npcWord 2 1 1)).fib
      = npcQ0 dat s 1 c₀ + polar q c₁ (lcOp s 1 1 c₀) :=
  npc_cross_operators dat hdat hV2 s u hu hVu 2 le_rfl 1 1 c₀ c₁

end StressTests

end Module

end GQ2.Dyadic.NpcJet
