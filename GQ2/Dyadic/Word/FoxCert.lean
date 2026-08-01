/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Opus-4.8 and Fable-5
-/
module

public import GQ2.Dyadic.Word.Fox

@[expose] public section

/-!
# Dyadic campaign, layer WW2: Fox certificates — row/col ops, replay, normal forms

The certificate layer over WW1's generic Fox evaluator (board WW2; plan §3 A1 "certificate
structures `FoxCertificate` (elementary row/col op lists + replay) — kernel `decide`/`rfl`
replay only, no CAS trust"): elementary row and column operations over formal operator
coefficients, the `applyOps` replay, normal-form targets, and the two certificate records
`FoxRowCertificate` (one Fox row, `(X → A) →+ A`) and `FoxCertificate` (the two-relator
Jacobian, `(X → A) →+ A × A`) in the ledger §3/§7 shape **ops list + target +
`verifies : applyOps … = target`**.

## Design (the WW1 interface rules, binding)

* **The certificate carrier is `foxDHom`/`foxJacobian` as `AddMonoidHom`s.**  Row operations
  act by *post*-composition on the codomain (`A × A`), column operations by *pre*-composition
  on the domain (`X → A`); `foxApplyOps` is literally
  `(rowOps).comp M |>.comp (colOps)`, so every replay step is `AddMonoidHom.comp`
  associativity — definitional (`rfl`).
* **Formal coefficients, interpreted per module class.**  A coefficient is a `FoxCoeff S`
  expression (formal `0, 1, +, ∘, −` over an atom alphabet `S`), evaluated into the
  endomorphism ring `AddMonoid.End A` by an interpretation `ρ : S → AddMonoid.End A`.  The
  standard alphabet `TameSym n` has the operator symbols of the ℚ₂ rows — `S = σ`, `T = τ`,
  `S₂ = σ₂` (integer powers of any marked letter and of `σ₂`) — **plus the `ω₂`-norm projector
  `P` as an opaque atom**: `P` is never computed, it is *assigned* per module class
  (`TameSym.splitEnd` sends it to `1`, `TameSym.ramifiedEnd` to `0`), which is exactly the
  split/ramified collapse of the engine lemmas `WordLift.powOmega2_u_of_trivial` /
  `WordLift.powOmega2_u_of_oddFixedPointFree`.  The split/unramified distinction is *not* a
  `ρ`-level distinction: both use `P ↦ 1`, and whether `S` (or `S₂`) acts trivially is a
  hypothesis of the instantiating theorem — mirroring the ℚ₂ row pairs, where `hU` is a
  hypothesis of the split row, not part of the coefficient data.  Lanes whose coefficients
  need atoms beyond `TameSym` (e.g. WNP's `A = σ^{η̂}`) instantiate the *same* generic layer
  at their own alphabet: every structure below is parametric in `S` and `ρ`.
* **Quantification "for every simple tame module."**  A wave-2 certificate is a *theorem*
  `∀ V t [class hypotheses], FoxRowCertificate (TameSym.splitEnd …) (foxDHom …)` whose ops
  list and target are fixed formal data — the same data at every module of the class; only
  the `verifies` proof (and the invertibility proofs) consume the class hypotheses.  The
  regression below states the `Γ_R` pins in exactly this shape.
* **Invertibility witnesses carried.**  Swaps and transvections are invertible outright
  (a transvection's witness is the slot-distinctness `g ≠ h`); a scale op carries its formal
  inverse `ψ` as *data*, and `Invertible ρ` asserts the two composites are `1` under `ρ`.
  The certificate records bundle the per-op proofs (`rowOps_invertible`/`colOps_invertible`),
  and the consumable conclusions (`mem_range_iff`, `mem_ker_iff`, `coker_defect_iff`,
  `card_ker`, `range_eq`) are exactly the transfers packet Prop. 4.1 needs: the lifting
  criterion, the defect-in-coker test and the `ker d¹`-torsor move between the evaluated
  Jacobian and its normal form.
* **`ω₂`-discipline.**  Replay is definitional except at `ω₂`-nodes; every `ω₂`-collapse in
  the regression routes through WW1's engine lemmas (already packaged in the hand-row lemmas
  `foxD_gammaRWildWord_split`/`_ramified` — `powOmega2` is **never unfolded** here).
* **Resolver correctness at the lift level.**  `PWord.evalFin_congr_of_orderOf_dvd` and its
  Fox-side forms (`foxEval_resolver_congr`, `foxD_resolver_congr`,
  `foxJacobian_resolver_congr`) state when two resolver pairs give the same evaluation: the
  integer values must agree modulo `2 · N` for `N` a uniform bound on base orders — the
  congruence-mod-`2·ord(base)` discipline of `WordLift.pow_eq_pow_of_modEq_two_mul` (the
  factor `2` is the lift level; a resolver correct only in the lower group halves the level
  and produces the falsely-zero derivative).  `ω₂` itself needs **no** resolver agreement —
  it is evaluated intrinsically — so the hypotheses quantify over `γ ≠ ω₂` only.  This is the
  module-level analogue of the parity reduction `evalZ_congr_of_parity`
  (`GQ2/Dyadic/Word/WordCoh.lean`, exponent-2 case); a joint hoist is a mechanical dedup for
  the orchestrator (still open after ticket WWH — the two live in files neither of which
  imports the other).
* **The `(A := …)` pitfall** (WW1 log): statements equating two `foxJacobian`s pin the
  coefficient module explicitly (`foxJacobian_resolver_congr` below does), else `Finite ?A`
  sticks.

## Regression (mandatory, board WW2): the `Γ_R` row end-to-end

`foxD_gammaRWildWord_split_apply` restates WW1's split row at arbitrary `Generator 1` offsets
(`a τ + (1 + S⁻¹)(a x₀)`) — since ticket WWH it lives with the hand rows it restates, in
`GQ2/Dyadic/Word/Fox.lean` — and the row is then run through full certificates at **every**
split simple tame module:

* `gammaRWildRowCert` — the published-row certificate: empty ops, target = the frozen row
  `(0, 1, 1 + S⁻¹, 0)` in the packet's column order `σ, τ, x₀, x₁` (per the frozen selection,
  `selection-freeze.md` row 1/SQ1, this is the `L_sq` base-case row for lane WL);
* `gammaRWildRowPivotCert` — the explicit-ops certificate: one column transvection clears the
  `x₀`-column against the `τ`-pivot, target = the standard row `(0, 1, 0, 0)`
  (`FoxRowNormalForm.single .tau`); replay is the `rfl`-level `foxRowApplyOps` step plus the
  hand-row collapse;
* `gammaRWildRowRamifiedCert` — the ramified twin: empty ops, target `(0, 0, S⁻¹, 0)` under
  `TameSym.ramifiedEnd` (`P ↦ 0`), mirroring the ℚ₂ split/ramified row pairs.

`demoCert` is the kernel-`decide` instance check: a two-row certificate over
`ZMod 2 × ZMod 2` (one row swap + one column transvection at a nontrivial operator atom)
whose `verifies` field is closed by `decide` — the "kernel-checkable verification on module
instances" clause of the WW2 spec, exercised on the ops/target algebra itself (a `foxDHom`
instance cannot be `decide`d past an `ω₂`-node: that collapse is engine-lemma territory by
the binding rules).

## Axiom state (recorded per WW2 instructions; `#print axioms` run in a scratch file, not
committed)

**Audited 2026-07-31, all named public `def`/`theorem` declarations of this file** (the
8 `inductive`/`structure` type declarations carry no proof content): every one depends on a
subset of the standard axioms `[propext, Classical.choice, Quot.sound]` (std-3), with zero
`sorryAx` and zero `native_decide` axioms.  In particular the headlines `foxApplyOps`,
`foxRowApplyOps`, `FoxCertificate.mem_range_iff`, `FoxCertificate.mem_ker_iff`,
`FoxCertificate.coker_defect_iff`, `FoxCertificate.card_ker`, `FoxRowCertificate.range_eq`,
`FoxRowCertificate.mem_ker_iff`, `FoxRowCertificate.card_ker`,
`FoxColOp.bijective_listHom`, `FoxRowOp.bijective_listHom`, `TameSym.toEnd`,
`PWord.evalFin_congr_of_orderOf_dvd`, `foxEval_resolver_congr`, `foxD_resolver_congr`,
`foxJacobian_resolver_congr`, `gammaRWildRowCert`, `gammaRWildRowPivotCert`,
`gammaRWildRowRamifiedCert` and `demoCert` all print exactly
`[propext, Classical.choice, Quot.sound]` (the remainder print strictly less: `[propext]`,
`[propext, Quot.sound]`, or none).  No sorries; no new axioms; kernel `decide` only (no
`native_decide`).  Re-audited after ticket WWH's hoists: the six declarations that moved to
`GQ2/Dyadic/Word/Fox.lean` (`WordLift.orderOf_dvd_two_mul`, `sum_generator_one`,
`q2OffsetsInv`, `q2Offsets_q2OffsetsInv`, `foxD_gammaRWildWord_split_apply`,
`foxD_gammaRWildWord_ramified_apply`) keep their prints there, and no print in this file grew.

## Implementation notes

`module`-style; the single in-repo import is `GQ2.Dyadic.Word.Fox` (module-style), which
supplies the evaluator, the engine lemmas and the regression rows.  This file does not
import `GQ2/Dyadic/MarkedCore/*` (layer-order rule) nor `GQ2/Dyadic/NpcJet/*`.
-/

namespace GQ2.Dyadic

open GQ2.FoxH

/-! ## Formal operator coefficients

The operator algebra of the board spec: formal expressions over an atom alphabet, evaluated
in the endomorphism ring of the coefficient module.  Kept as a bare inductive (not a free
algebra) so that certificate data is canonical, `DecidableEq`, `Repr`-printable, and
kernel-reduces under `decide`. -/

/-- A **formal operator coefficient** over the atom alphabet `S`: the expressions
`0, 1, atom, +, ∘, −` of the operator algebra.  Evaluation into `AddMonoid.End A` is
`FoxCoeff.eval`; `comp` evaluates to ring multiplication (composition) there.  Over the
elementary (char-2) modules of the campaign `neg` evaluates to the identity operation, but it
is kept in the grammar so that transvection inverses exist at the formal level over any
coefficient module. -/
inductive FoxCoeff (S : Type*)
  /-- The zero operator. -/
  | zero
  /-- The identity operator. -/
  | one
  /-- An atomic operator symbol. -/
  | atom (s : S)
  /-- Pointwise sum of operators. -/
  | add (p q : FoxCoeff S)
  /-- Composition of operators (ring multiplication in `AddMonoid.End A`). -/
  | comp (p q : FoxCoeff S)
  /-- Pointwise negation of an operator. -/
  | neg (p : FoxCoeff S)
  deriving DecidableEq, Repr

namespace FoxCoeff

variable {S : Type*} {A : Type*} [AddCommGroup A]

/-- **Evaluation of a formal coefficient** under an atom interpretation
`ρ : S → AddMonoid.End A`: the unique extension to the operator expressions, valued in the
endomorphism ring. -/
def eval (ρ : S → AddMonoid.End A) : FoxCoeff S → AddMonoid.End A
  | .zero => 0
  | .one => 1
  | .atom s => ρ s
  | .add p q => eval ρ p + eval ρ q
  | .comp p q => eval ρ p * eval ρ q
  | .neg p => -eval ρ p

variable (ρ : S → AddMonoid.End A)

/-! Operator-level equations (for `Invertible`-condition algebra; deliberately not `simp` —
the pointwise `_apply` forms below are the simp normal form, so that bare `AddMonoid.End`
arithmetic never surfaces in replay goals). -/

theorem eval_zero : eval ρ .zero = 0 := rfl
theorem eval_one : eval ρ .one = 1 := rfl
theorem eval_atom (s : S) : eval ρ (.atom s) = ρ s := rfl
theorem eval_add (p q : FoxCoeff S) : eval ρ (.add p q) = eval ρ p + eval ρ q := rfl
theorem eval_comp (p q : FoxCoeff S) : eval ρ (.comp p q) = eval ρ p * eval ρ q := rfl
theorem eval_neg (p : FoxCoeff S) : eval ρ (.neg p) = -eval ρ p := rfl

/-! Pointwise application forms (all `rfl`): the shapes certificate replays rewrite with. -/

@[simp] theorem eval_zero_apply (v : A) : eval ρ (.zero : FoxCoeff S) v = 0 := rfl
@[simp] theorem eval_one_apply (v : A) : eval ρ (.one : FoxCoeff S) v = v := rfl
@[simp] theorem eval_atom_apply (s : S) (v : A) : eval ρ (.atom s) v = ρ s v := rfl
@[simp] theorem eval_add_apply (p q : FoxCoeff S) (v : A) :
    eval ρ (.add p q) v = eval ρ p v + eval ρ q v := rfl
@[simp] theorem eval_comp_apply (p q : FoxCoeff S) (v : A) :
    eval ρ (.comp p q) v = eval ρ p (eval ρ q v) := rfl
@[simp] theorem eval_neg_apply (p : FoxCoeff S) (v : A) :
    eval ρ (.neg p) v = -eval ρ p v := rfl

end FoxCoeff

/-! ## The standard atom alphabet: `S`, `T`, `S₂`, and the projector `P`

The symbols of the ℚ₂ operator identities (`pairingR_operator_injective` chain,
`GQ2/Roe/Hessian.lean`): integer powers of the marked letters (`S = gen .sigma 1`,
`S⁻¹ = gen .sigma (−1)`, `T = gen .tau 1`, `B = gen .sigma (2^r)`, …), integer powers of
`σ₂ = σ^{ω₂}`, and the `ω₂`-norm projector `P` as an *opaque* atom whose value is assigned
per module class — `1` in the split/unramified collapse, `0` in the ramified collapse,
exactly the two engine-lemma readings.  `powOmega2` appears only inside the *interpretation*
of `sigma2` and is never unfolded. -/

/-- The **standard atom alphabet** of the dyadic Fox certificates over `Generator n`. -/
inductive TameSym (n : ℕ)
  /-- The action of the `k`-th power of the marked letter `g` (`S = gen .sigma 1`, etc.). -/
  | gen (g : Generator n) (k : ℤ)
  /-- The action of the `k`-th power of `σ₂ = σ^{ω₂}`. -/
  | sigma2 (k : ℤ)
  /-- The `ω₂`-norm projector `P`, assigned per module class (split `1`, ramified `0`). -/
  | proj
  deriving DecidableEq, Repr

namespace TameSym

variable {n : ℕ} {C : Type*} [Group C] {A : Type*} [AddCommGroup A] [DistribMulAction C A]

/-- **The standard interpretation** of the atom alphabet at a marking `t` with projector
assignment `π`: `gen g k` acts as `(t g)^k`, `sigma2 k` as `(powOmega2 t.σ)^k`, and the
opaque projector as `π`. -/
noncomputable def toEnd (t : Marking n C) (π : AddMonoid.End A) : TameSym n → AddMonoid.End A
  | .gen g k => DistribMulAction.toAddMonoidEnd C A ((t g) ^ k)
  | .sigma2 k => DistribMulAction.toAddMonoidEnd C A ((powOmega2 t.σ) ^ k)
  | .proj => π

variable (t : Marking n C) (π : AddMonoid.End A)

@[simp] theorem toEnd_gen_apply (g : Generator n) (k : ℤ) (v : A) :
    toEnd t π (.gen g k) v = ((t g) ^ k) • v := rfl

@[simp] theorem toEnd_sigma2_apply (k : ℤ) (v : A) :
    toEnd t π (.sigma2 k) v = ((powOmega2 t.σ) ^ k) • v := rfl

@[simp] theorem toEnd_proj : toEnd t π .proj = π := rfl

/-- **The split/unramified interpretation**: the projector collapses to the identity
(`WordLift.powOmega2_u_of_trivial`).  Whether `S` or `S₂` additionally acts trivially is a
hypothesis of the instantiating theorem, not part of the interpretation — mirroring the ℚ₂
row pairs. -/
noncomputable abbrev splitEnd (t : Marking n C) : TameSym n → AddMonoid.End A := toEnd t 1

/-- **The ramified interpretation**: the projector collapses to zero
(`WordLift.powOmega2_u_of_oddFixedPointFree`). -/
noncomputable abbrev ramifiedEnd (t : Marking n C) : TameSym n → AddMonoid.End A := toEnd t 0

/-- A trivially-acting marked letter evaluates to the identity operator, at every power —
the class-collapse lemma for `gen` atoms (the ℚ₂ hypotheses `hx0`/`hx1`/`htau`/`hU` in
operator form). -/
theorem toEnd_gen_of_trivial {g : Generator n} (hg : ∀ v : A, t g • v = v) (k : ℤ) :
    toEnd t π (.gen g k) = 1 :=
  AddMonoidHom.ext fun v =>
    MulAction.mem_stabilizer_iff.mp
      ((MulAction.stabilizer C v).zpow_mem (MulAction.mem_stabilizer_iff.mpr (hg v)) k)

/-- A trivially-acting `σ₂` evaluates to the identity operator, at every power — the
class-collapse lemma for `sigma2` atoms (the `hU` hypothesis of the `Γ_A` split row). -/
theorem toEnd_sigma2_of_trivial (hU : ∀ v : A, powOmega2 t.σ • v = v) (k : ℤ) :
    toEnd t π (.sigma2 k) = 1 :=
  AddMonoidHom.ext fun v =>
    MulAction.mem_stabilizer_iff.mp
      ((MulAction.stabilizer C v).zpow_mem (MulAction.mem_stabilizer_iff.mpr (hU v)) k)

end TameSym

/-! ## Elementary column operations

A column operation acts on the *domain* `X → A` of a Fox matrix (one slot per marked
generator) and is applied to a matrix by **pre-composition**.  The three kinds are the
elementary moves of the ledger: slot exchange, transvection (add an operator multiple of one
slot to another — this changes the *other* column of the matrix), and scaling a slot by an
operator carrying a formal inverse. -/

/-- An **elementary column operation** over the formal coefficients `FoxCoeff S`.

* `swap g h` — exchange the `g` and `h` slots.
* `transvect g h φ` — add `φ` applied to the `h`-slot to the `g`-slot (matrix effect: the
  `h`-column gains `c_g ∘ φ`).  Invertible whenever `g ≠ h` (`Invertible`).
* `scale g φ ψ` — apply `φ` to the `g`-slot; the formal inverse `ψ` is **carried as data**,
  and `Invertible` asserts the two composites are `1` under the interpretation. -/
inductive FoxColOp (X : Type*) (S : Type*)
  /-- Exchange the `g` and `h` slots. -/
  | swap (g h : X)
  /-- Add `φ` applied to the `h`-slot to the `g`-slot. -/
  | transvect (g h : X) (φ : FoxCoeff S)
  /-- Apply `φ` to the `g`-slot, with formal inverse `ψ` carried. -/
  | scale (g : X) (φ ψ : FoxCoeff S)
  deriving DecidableEq

namespace FoxColOp

variable {X S : Type*} [DecidableEq X] {A : Type*} [AddCommGroup A]
  (ρ : S → AddMonoid.End A)

/-- **The forward action of a column operation** on the domain `X → A`, as an additive
homomorphism (applied to a Fox matrix by pre-composition). -/
def toHom : FoxColOp X S → ((X → A) →+ (X → A))
  | .swap g h => AddMonoidHom.mk' (fun a => a ∘ Equiv.swap g h) fun _ _ => rfl
  | .transvect g h φ =>
      AddMonoidHom.mk' (fun a k => a k + if k = g then φ.eval ρ (a h) else 0) fun a b => by
        funext k
        by_cases hk : k = g
        · subst hk
          simp only [Pi.add_apply, map_add]
          abel
        · simp [hk]
  | .scale g φ _ =>
      AddMonoidHom.mk' (fun a k => if k = g then φ.eval ρ (a k) else a k) fun a b => by
        funext k
        by_cases hk : k = g <;> simp [hk]

@[simp] theorem toHom_swap_apply (g h : X) (a : X → A) (k : X) :
    toHom ρ (.swap g h) a k = a (Equiv.swap g h k) := rfl

@[simp] theorem toHom_transvect_apply (g h : X) (φ : FoxCoeff S) (a : X → A) (k : X) :
    toHom ρ (.transvect g h φ) a k = a k + if k = g then φ.eval ρ (a h) else 0 := rfl

@[simp] theorem toHom_scale_apply (g : X) (φ ψ : FoxCoeff S) (a : X → A) (k : X) :
    toHom ρ (.scale g φ ψ) a k = if k = g then φ.eval ρ (a k) else a k := rfl

/-- **The invertibility witness condition** of a column operation under the interpretation
`ρ`: swaps are free, a transvection's witness is slot-distinctness, a scale op's witness is
that its carried formal inverse really is a two-sided inverse. -/
def Invertible : FoxColOp X S → Prop
  | .swap _ _ => True
  | .transvect g h _ => g ≠ h
  | .scale _ φ ψ => φ.eval ρ * ψ.eval ρ = 1 ∧ ψ.eval ρ * φ.eval ρ = 1

/-- An invertible column operation acts bijectively on the domain. -/
theorem bijective_toHom : ∀ {c : FoxColOp X S}, c.Invertible ρ → Function.Bijective (toHom ρ c)
  | .swap g h, _ => by
      refine Function.bijective_iff_has_inverse.mpr ⟨toHom ρ (.swap g h), fun a => ?_, fun a => ?_⟩
        <;> · funext k
              simp [Equiv.swap_apply_self]
  | .transvect g h φ, hgh => by
      refine Function.bijective_iff_has_inverse.mpr
        ⟨toHom ρ (.transvect g h φ.neg), fun a => ?_, fun a => ?_⟩ <;>
      · funext k
        by_cases hk : k = g
        · subst hk
          simp [Ne.symm hgh]
        · simp [hk]
  | .scale g φ ψ, ⟨h₁, h₂⟩ => by
      refine Function.bijective_iff_has_inverse.mpr
        ⟨toHom ρ (.scale g ψ φ), fun a => ?_, fun a => ?_⟩
      · funext k
        by_cases hk : k = g
        · subst hk
          simpa using DFunLike.congr_fun h₂ (a k)
        · simp [hk]
      · funext k
        by_cases hk : k = g
        · subst hk
          simpa using DFunLike.congr_fun h₁ (a k)
        · simp [hk]

/-- **The composite action of a list of column operations, head applied first**: applying
`c :: cs` to a matrix `M` is applying `cs` to `M.comp (c.toHom ρ)`, so the composite
homomorphism is `c₁ ∘ (c₂ ∘ ⋯)`. -/
def listHom : List (FoxColOp X S) → ((X → A) →+ (X → A))
  | [] => AddMonoidHom.id _
  | c :: cs => (toHom ρ c).comp (listHom cs)

@[simp] theorem listHom_nil : listHom ρ ([] : List (FoxColOp X S)) = AddMonoidHom.id _ := rfl

@[simp] theorem listHom_cons (c : FoxColOp X S) (cs : List (FoxColOp X S)) :
    listHom ρ (c :: cs) = (toHom ρ c).comp (listHom ρ cs) := rfl

/-- A list of invertible column operations composes to a bijection. -/
theorem bijective_listHom {cs : List (FoxColOp X S)} (h : ∀ c ∈ cs, c.Invertible ρ) :
    Function.Bijective (listHom ρ cs) := by
  induction cs with
  | nil => exact Function.bijective_id
  | cons c cs ih =>
      rw [listHom_cons, AddMonoidHom.coe_comp]
      exact (bijective_toHom ρ (h c List.mem_cons_self)).comp
        (ih fun d hd => h d (List.mem_cons_of_mem c hd))

end FoxColOp

/-! ## Elementary row operations

A row operation acts on the *codomain* `A × A` of the two-relator Jacobian (one coordinate
per relator) and is applied by **post-composition**. -/

/-- An **elementary row operation** on a two-row Fox system over the formal coefficients.

* `swap` — exchange the two rows.
* `addFst φ`/`addSnd φ` — add an operator multiple of the other row (always invertible).
* `scaleFst φ ψ`/`scaleSnd φ ψ` — scale one row, formal inverse `ψ` carried as data. -/
inductive FoxRowOp (S : Type*)
  /-- Exchange the two rows. -/
  | swap
  /-- Add `φ` applied to the second row to the first. -/
  | addFst (φ : FoxCoeff S)
  /-- Add `φ` applied to the first row to the second. -/
  | addSnd (φ : FoxCoeff S)
  /-- Scale the first row by `φ`, with formal inverse `ψ` carried. -/
  | scaleFst (φ ψ : FoxCoeff S)
  /-- Scale the second row by `φ`, with formal inverse `ψ` carried. -/
  | scaleSnd (φ ψ : FoxCoeff S)
  deriving DecidableEq

namespace FoxRowOp

variable {S : Type*} {A : Type*} [AddCommGroup A] (ρ : S → AddMonoid.End A)

/-- **The forward action of a row operation** on `A × A` (applied to a Fox matrix by
post-composition). -/
def toHom : FoxRowOp S → (A × A →+ A × A)
  | .swap => AddMonoidHom.mk' (fun p => (p.2, p.1)) fun _ _ => rfl
  | .addFst φ =>
      AddMonoidHom.mk' (fun p => (p.1 + φ.eval ρ p.2, p.2)) fun p q => by
        ext
        · simp only [Prod.fst_add, Prod.snd_add, map_add]
          abel
        · rfl
  | .addSnd φ =>
      AddMonoidHom.mk' (fun p => (p.1, p.2 + φ.eval ρ p.1)) fun p q => by
        ext
        · rfl
        · simp only [Prod.fst_add, Prod.snd_add, map_add]
          abel
  | .scaleFst φ _ =>
      AddMonoidHom.mk' (fun p => (φ.eval ρ p.1, p.2)) fun p q => by ext <;> simp
  | .scaleSnd φ _ =>
      AddMonoidHom.mk' (fun p => (p.1, φ.eval ρ p.2)) fun p q => by ext <;> simp

@[simp] theorem toHom_swap_apply (p : A × A) : toHom ρ (.swap : FoxRowOp S) p = (p.2, p.1) := rfl

@[simp] theorem toHom_addFst_apply (φ : FoxCoeff S) (p : A × A) :
    toHom ρ (.addFst φ) p = (p.1 + φ.eval ρ p.2, p.2) := rfl

@[simp] theorem toHom_addSnd_apply (φ : FoxCoeff S) (p : A × A) :
    toHom ρ (.addSnd φ) p = (p.1, p.2 + φ.eval ρ p.1) := rfl

@[simp] theorem toHom_scaleFst_apply (φ ψ : FoxCoeff S) (p : A × A) :
    toHom ρ (.scaleFst φ ψ) p = (φ.eval ρ p.1, p.2) := rfl

@[simp] theorem toHom_scaleSnd_apply (φ ψ : FoxCoeff S) (p : A × A) :
    toHom ρ (.scaleSnd φ ψ) p = (p.1, φ.eval ρ p.2) := rfl

/-- **The invertibility witness condition** of a row operation under `ρ`. -/
def Invertible : FoxRowOp S → Prop
  | .swap => True
  | .addFst _ => True
  | .addSnd _ => True
  | .scaleFst φ ψ => φ.eval ρ * ψ.eval ρ = 1 ∧ ψ.eval ρ * φ.eval ρ = 1
  | .scaleSnd φ ψ => φ.eval ρ * ψ.eval ρ = 1 ∧ ψ.eval ρ * φ.eval ρ = 1

/-- An invertible row operation acts bijectively on `A × A`. -/
theorem bijective_toHom : ∀ {r : FoxRowOp S}, r.Invertible ρ → Function.Bijective (toHom ρ r)
  | .swap, _ =>
      Function.bijective_iff_has_inverse.mpr ⟨toHom ρ .swap, fun _ => rfl, fun _ => rfl⟩
  | .addFst φ, _ => by
      refine Function.bijective_iff_has_inverse.mpr
        ⟨toHom ρ (.addFst φ.neg), fun p => ?_, fun p => ?_⟩ <;>
      · ext
        · simp
        · rfl
  | .addSnd φ, _ => by
      refine Function.bijective_iff_has_inverse.mpr
        ⟨toHom ρ (.addSnd φ.neg), fun p => ?_, fun p => ?_⟩ <;>
      · ext
        · rfl
        · simp
  | .scaleFst φ ψ, ⟨h₁, h₂⟩ => by
      refine Function.bijective_iff_has_inverse.mpr
        ⟨toHom ρ (.scaleFst ψ φ), fun p => ?_, fun p => ?_⟩
      · ext
        · simpa using DFunLike.congr_fun h₂ p.1
        · rfl
      · ext
        · simpa using DFunLike.congr_fun h₁ p.1
        · rfl
  | .scaleSnd φ ψ, ⟨h₁, h₂⟩ => by
      refine Function.bijective_iff_has_inverse.mpr
        ⟨toHom ρ (.scaleSnd ψ φ), fun p => ?_, fun p => ?_⟩
      · ext
        · rfl
        · simpa using DFunLike.congr_fun h₂ p.2
      · ext
        · rfl
        · simpa using DFunLike.congr_fun h₁ p.2

/-- The composite action of a list of row operations, head applied first. -/
def listHom : List (FoxRowOp S) → (A × A →+ A × A)
  | [] => AddMonoidHom.id _
  | r :: rs => (listHom rs).comp (toHom ρ r)

@[simp] theorem listHom_nil : listHom ρ ([] : List (FoxRowOp S)) = AddMonoidHom.id _ := rfl

@[simp] theorem listHom_cons (r : FoxRowOp S) (rs : List (FoxRowOp S)) :
    listHom ρ (r :: rs) = (listHom ρ rs).comp (toHom ρ r) := rfl

/-- A list of invertible row operations composes to a bijection. -/
theorem bijective_listHom {rs : List (FoxRowOp S)} (h : ∀ r ∈ rs, r.Invertible ρ) :
    Function.Bijective (listHom ρ rs) := by
  induction rs with
  | nil => exact Function.bijective_id
  | cons r rs ih =>
      rw [listHom_cons, AddMonoidHom.coe_comp]
      exact (ih fun s hs => h s (List.mem_cons_of_mem r hs)).comp
        (bijective_toHom ρ (h r List.mem_cons_self))

end FoxRowOp

/-! ## The replay

Row operations post-compose, column operations pre-compose; the replay of a whole
certificate is a single `comp` chain, so the per-op step lemmas are `rfl`. -/

section Replay

variable {X S : Type*} [DecidableEq X] {A : Type*} [AddCommGroup A]
  (ρ : S → AddMonoid.End A)

/-- **The certificate replay** (board WW2; plan §3 A1): apply a list of row operations and a
list of column operations to a Fox matrix `M : (X → A) →+ A × A` by post/pre-composition —
the two-relator-Jacobian form, `M = foxJacobian t E E₂ R₁ R₂`. -/
def foxApplyOps (rops : List (FoxRowOp S)) (cops : List (FoxColOp X S))
    (M : (X → A) →+ A × A) : (X → A) →+ A × A :=
  ((FoxRowOp.listHom ρ rops).comp M).comp (FoxColOp.listHom ρ cops)

@[simp] theorem foxApplyOps_apply (rops : List (FoxRowOp S)) (cops : List (FoxColOp X S))
    (M : (X → A) →+ A × A) (a : X → A) :
    foxApplyOps ρ rops cops M a
      = FoxRowOp.listHom ρ rops (M (FoxColOp.listHom ρ cops a)) := rfl

@[simp] theorem foxApplyOps_nil_nil (M : (X → A) →+ A × A) :
    foxApplyOps ρ ([] : List (FoxRowOp S)) ([] : List (FoxColOp X S)) M = M := rfl

/-- Replay step, row side (`rfl`): applying `r :: rops` is applying `rops` to the
`r`-post-composed matrix. -/
theorem foxApplyOps_cons_row (r : FoxRowOp S) (rops : List (FoxRowOp S))
    (cops : List (FoxColOp X S)) (M : (X → A) →+ A × A) :
    foxApplyOps ρ (r :: rops) cops M
      = foxApplyOps ρ rops cops ((FoxRowOp.toHom ρ r).comp M) := rfl

/-- Replay step, column side (`rfl`): applying `c :: cops` is applying `cops` to the
`c`-pre-composed matrix. -/
theorem foxApplyOps_cons_col (rops : List (FoxRowOp S)) (c : FoxColOp X S)
    (cops : List (FoxColOp X S)) (M : (X → A) →+ A × A) :
    foxApplyOps ρ rops (c :: cops) M
      = foxApplyOps ρ rops cops (M.comp (FoxColOp.toHom ρ c)) := rfl

/-- **The single-row replay**: column operations only, pre-composed onto one Fox row
`M = foxDHom t E E₂ w`. -/
def foxRowApplyOps (cops : List (FoxColOp X S)) (M : (X → A) →+ A) : (X → A) →+ A :=
  M.comp (FoxColOp.listHom ρ cops)

@[simp] theorem foxRowApplyOps_apply (cops : List (FoxColOp X S)) (M : (X → A) →+ A)
    (a : X → A) : foxRowApplyOps ρ cops M a = M (FoxColOp.listHom ρ cops a) := rfl

@[simp] theorem foxRowApplyOps_nil (M : (X → A) →+ A) :
    foxRowApplyOps ρ ([] : List (FoxColOp X S)) M = M := rfl

/-- Single-row replay step (`rfl`). -/
theorem foxRowApplyOps_cons (c : FoxColOp X S) (cops : List (FoxColOp X S))
    (M : (X → A) →+ A) :
    foxRowApplyOps ρ (c :: cops) M = foxRowApplyOps ρ cops (M.comp (FoxColOp.toHom ρ c)) := rfl

end Replay

/-! ## Normal-form targets

A normal form is a formal matrix: one `FoxCoeff` per generator slot per row, denoting the
homomorphism `a ↦ Σ_g coeff_g (a g)` under an interpretation. -/

/-- A **single-row normal-form target**: a formal coefficient per generator slot. -/
structure FoxRowNormalForm (X : Type*) (S : Type*) where
  /-- The formal coefficient of the `g`-column. -/
  row : X → FoxCoeff S

namespace FoxRowNormalForm

/-- The **standard (pivot) row** at `g₀`: coefficient `1` in the `g₀`-column, `0` elsewhere. -/
def single {X S : Type*} [DecidableEq X] (g₀ : X) : FoxRowNormalForm X S :=
  ⟨fun g => if g = g₀ then .one else .zero⟩

@[simp] theorem single_row {X S : Type*} [DecidableEq X] (g₀ g : X) :
    (single (S := S) g₀).row g = if g = g₀ then .one else .zero := rfl

variable {X S : Type*} [Fintype X] {A : Type*} [AddCommGroup A]
  (ρ : S → AddMonoid.End A)

/-- The homomorphism denoted by a row normal form: `a ↦ Σ_g coeff_g (a g)`. -/
def toHom (nf : FoxRowNormalForm X S) : (X → A) →+ A :=
  AddMonoidHom.mk' (fun a => ∑ g, (nf.row g).eval ρ (a g)) fun a b => by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun g _ => by rw [Pi.add_apply, map_add]

@[simp] theorem toHom_apply (nf : FoxRowNormalForm X S) (a : X → A) :
    nf.toHom ρ a = ∑ g, (nf.row g).eval ρ (a g) := rfl

/-- The pivot row denotes evaluation at the pivot slot. -/
@[simp] theorem single_toHom_apply [DecidableEq X] (g₀ : X) (a : X → A) :
    (single g₀).toHom ρ a = a g₀ := by
  rw [toHom_apply]
  have h : ∀ g, ((single (S := S) g₀).row g).eval ρ (a g) = if g = g₀ then a g else 0 := by
    intro g
    by_cases hg : g = g₀ <;> simp [hg]
  rw [Finset.sum_congr rfl fun g _ => h g, Finset.sum_ite_eq' Finset.univ g₀ a,
    if_pos (Finset.mem_univ g₀)]

end FoxRowNormalForm

/-- A **two-row normal-form target** for the evaluated two-relator Jacobian. -/
structure FoxNormalForm (X : Type*) (S : Type*) where
  /-- The first (e.g. tame-relator) row. -/
  fst : FoxRowNormalForm X S
  /-- The second (e.g. wild-relator) row. -/
  snd : FoxRowNormalForm X S

namespace FoxNormalForm

variable {X S : Type*} [Fintype X] {A : Type*} [AddCommGroup A]
  (ρ : S → AddMonoid.End A)

/-- The homomorphism denoted by a two-row normal form. -/
def toHom (nf : FoxNormalForm X S) : (X → A) →+ A × A :=
  (nf.fst.toHom ρ).prod (nf.snd.toHom ρ)

@[simp] theorem toHom_apply (nf : FoxNormalForm X S) (a : X → A) :
    nf.toHom ρ a = (nf.fst.toHom ρ a, nf.snd.toHom ρ a) := rfl

end FoxNormalForm

/-! ## The certificates (ledger §3/§7 shape)

Ops list + target + `verifies : applyOps … = target`, with the invertibility witnesses of
every listed op bundled.  The matrix `M` is a *parameter*, so a certificate value pins the
certified Jacobian (and with it the coefficient module — the `(A := …)` discipline) in its
type. -/

/-- **The Fox certificate** for a two-relator Jacobian `M : (X → A) →+ A × A` (board WW2;
ledger §3/§7 shape): elementary op lists, a normal-form target, the carried invertibility
witnesses, and the replay identity.  Instantiate at `M = foxJacobian t E E₂ R₁ R₂`. -/
structure FoxCertificate {X S A : Type*} [Fintype X] [DecidableEq X] [AddCommGroup A]
    (ρ : S → AddMonoid.End A) (M : (X → A) →+ A × A) where
  /-- The row operations, head applied first. -/
  rowOps : List (FoxRowOp S)
  /-- The column operations, head applied first. -/
  colOps : List (FoxColOp X S)
  /-- The normal-form target. -/
  target : FoxNormalForm X S
  /-- Invertibility witnesses for every listed row operation. -/
  rowOps_invertible : ∀ r ∈ rowOps, r.Invertible ρ
  /-- Invertibility witnesses for every listed column operation. -/
  colOps_invertible : ∀ c ∈ colOps, c.Invertible ρ
  /-- The replay identity: applying the ops to `M` yields the target. -/
  verifies : foxApplyOps ρ rowOps colOps M = target.toHom ρ

namespace FoxCertificate

variable {X S A : Type*} [Fintype X] [DecidableEq X] [AddCommGroup A]
  {ρ : S → AddMonoid.End A} {M : (X → A) →+ A × A} (cert : FoxCertificate ρ M)

/-- **The lifting-criterion transfer** (packet Prop. 4.1(1) consumable): a defect lies in the
range of the evaluated Jacobian iff its row-transformed image lies in the range of the normal
form.  Feeds `foxLifts_iff` on the target side. -/
theorem mem_range_iff (y : A × A) :
    y ∈ M.range ↔ FoxRowOp.listHom ρ cert.rowOps y ∈ (cert.target.toHom ρ).range := by
  have hrow := FoxRowOp.bijective_listHom ρ cert.rowOps_invertible
  have hcol := FoxColOp.bijective_listHom ρ cert.colOps_invertible
  constructor
  · rintro ⟨x, rfl⟩
    obtain ⟨a, rfl⟩ := hcol.surjective x
    exact ⟨a, by rw [← cert.verifies]; rfl⟩
  · rintro ⟨a, ha⟩
    rw [← cert.verifies, foxApplyOps_apply] at ha
    exact ⟨FoxColOp.listHom ρ cert.colOps a, hrow.injective ha⟩

/-- **The defect-in-cokernel transfer** (packet Prop. 4.1(1), cokernel form consumable): the
defect class vanishes in `coker M` iff the row-transformed defect class vanishes in the coker
of the normal form.  Feeds `foxLifts_iff_coker` on the target side. -/
theorem coker_defect_iff (y : A × A) :
    (QuotientAddGroup.mk y : (A × A) ⧸ M.range) = 0
      ↔ (QuotientAddGroup.mk (FoxRowOp.listHom ρ cert.rowOps y)
          : (A × A) ⧸ (cert.target.toHom ρ).range) = 0 := by
  rw [QuotientAddGroup.eq_zero_iff, QuotientAddGroup.eq_zero_iff]
  exact cert.mem_range_iff y

/-- **The kernel transfer** (packet Prop. 4.1(2) consumable): an offset vector is killed by
the normal form iff its column-transformed image is killed by the Jacobian — the
`ker d¹`-torsor of the lifting problem is computed on the target. -/
theorem mem_ker_iff (a : X → A) :
    a ∈ (cert.target.toHom ρ).ker ↔ FoxColOp.listHom ρ cert.colOps a ∈ M.ker := by
  have hrow := FoxRowOp.bijective_listHom ρ cert.rowOps_invertible
  rw [AddMonoidHom.mem_ker, AddMonoidHom.mem_ker, ← cert.verifies, foxApplyOps_apply]
  constructor
  · intro h
    exact hrow.injective (h.trans (map_zero _).symm)
  · intro h
    rw [h, map_zero]

/-- **The kernel cardinality transfer**: the target's kernel and the Jacobian's kernel are
equinumerous (the column composite restricts to a bijection between them). -/
theorem card_ker : Nat.card (cert.target.toHom ρ).ker = Nat.card M.ker := by
  have hcol := FoxColOp.bijective_listHom ρ cert.colOps_invertible
  refine Nat.card_congr (Equiv.ofBijective
    (fun a => ⟨FoxColOp.listHom ρ cert.colOps a.1, (cert.mem_ker_iff a.1).mp a.2⟩) ⟨?_, ?_⟩)
  · intro a b hab
    exact Subtype.ext (hcol.injective (congrArg Subtype.val hab))
  · rintro ⟨x, hx⟩
    obtain ⟨a, rfl⟩ := hcol.surjective x
    exact ⟨⟨a, (cert.mem_ker_iff a).mpr hx⟩, rfl⟩

end FoxCertificate

/-- **The single-row Fox certificate** for one Fox row `M : (X → A) →+ A` (column operations
only): ops list + target + `verifies`.  Instantiate at `M = foxDHom t E E₂ w`. -/
structure FoxRowCertificate {X S A : Type*} [Fintype X] [DecidableEq X] [AddCommGroup A]
    (ρ : S → AddMonoid.End A) (M : (X → A) →+ A) where
  /-- The column operations, head applied first. -/
  colOps : List (FoxColOp X S)
  /-- The normal-form target row. -/
  target : FoxRowNormalForm X S
  /-- Invertibility witnesses for every listed column operation. -/
  colOps_invertible : ∀ c ∈ colOps, c.Invertible ρ
  /-- The replay identity. -/
  verifies : foxRowApplyOps ρ colOps M = target.toHom ρ

namespace FoxRowCertificate

variable {X S A : Type*} [Fintype X] [DecidableEq X] [AddCommGroup A]
  {ρ : S → AddMonoid.End A} {M : (X → A) →+ A} (cert : FoxRowCertificate ρ M)

/-- **The range of a certified row equals the range of its normal form** (no row operations
on a single row, so the ranges agree on the nose). -/
theorem range_eq : (cert.target.toHom ρ).range = M.range := by
  have hcol := FoxColOp.bijective_listHom ρ cert.colOps_invertible
  ext y
  constructor
  · rintro ⟨a, rfl⟩
    exact ⟨FoxColOp.listHom ρ cert.colOps a, by rw [← cert.verifies]; rfl⟩
  · rintro ⟨x, rfl⟩
    obtain ⟨a, rfl⟩ := hcol.surjective x
    exact ⟨a, by rw [← cert.verifies]; rfl⟩

/-- The kernel transfer for a certified row. -/
theorem mem_ker_iff (a : X → A) :
    a ∈ (cert.target.toHom ρ).ker ↔ FoxColOp.listHom ρ cert.colOps a ∈ M.ker := by
  rw [AddMonoidHom.mem_ker, AddMonoidHom.mem_ker, ← cert.verifies]
  exact Iff.rfl

/-- The kernel cardinality transfer for a certified row. -/
theorem card_ker : Nat.card (cert.target.toHom ρ).ker = Nat.card M.ker := by
  have hcol := FoxColOp.bijective_listHom ρ cert.colOps_invertible
  refine Nat.card_congr (Equiv.ofBijective
    (fun a => ⟨FoxColOp.listHom ρ cert.colOps a.1, (cert.mem_ker_iff a.1).mp a.2⟩) ⟨?_, ?_⟩)
  · intro a b hab
    exact Subtype.ext (hcol.injective (congrArg Subtype.val hab))
  · rintro ⟨x, hx⟩
    obtain ⟨a, rfl⟩ := hcol.surjective x
    exact ⟨⟨a, (cert.mem_ker_iff a).mpr hx⟩, rfl⟩

end FoxRowCertificate

/-! ## Resolver correctness at the lift level

The binding WW1 rule: a resolver must be correct **at the order of the lifted element**, and
lifts double levels — `WordLift.pow_eq_pow_of_modEq_two_mul` sees exponents only modulo
`2 · ord(base)`.  The uniform statement: over a group all of whose element orders divide `M`,
the finite denotation only sees resolver values modulo `M`; on the lift group `WordLift A C`
with elementary `A`, orders divide `2 · N` for any uniform base bound `N`
(`WordLift.orderOf_dvd_two_mul`), so resolver pairs agreeing modulo `2 · N` are
interchangeable.  `ω₂` is exempt — `evalFin` evaluates it intrinsically, which is why the
hypotheses below quantify over `γ ≠ ω₂` only. -/

section Resolver

/-- **Resolver congruence for the finite denotation**: if every element order of `G` divides
`M` and two resolver pairs agree modulo `M` (at every non-`ω₂` profinite exponent and every
`ℤ₂`-exponent), the finite denotations agree at every marking.  The `M = 2` case is the
parity reduction `evalZ_congr_of_parity` of `GQ2/Dyadic/Word/WordCoh.lean` in `evalFin` form
(dedup note: a joint hoist is mechanical). -/
theorem PWord.evalFin_congr_of_orderOf_dvd {X : Type*} {G : Type*} [Group G] {M : ℕ}
    (hG : ∀ x : G, orderOf x ∣ M) (μ : X → G) {E E' : Zhat → ℤ} {E₂ E₂' : ℤ_[2] → ℤ}
    (hE : ∀ γ : Zhat, γ ≠ omega2 → E γ ≡ E' γ [ZMOD M])
    (hE₂ : ∀ z : ℤ_[2], E₂ z ≡ E₂' z [ZMOD M]) (w : PWord X) :
    PWord.evalFin μ E E₂ w = PWord.evalFin μ E' E₂' w := by
  have key : ∀ (x : G) {k l : ℤ}, k ≡ l [ZMOD M] → x ^ k = x ^ l := fun x _ _ h =>
    zpow_eq_zpow_iff_modEq.mpr (h.of_dvd (Int.natCast_dvd_natCast.mpr (hG x)))
  induction w with
  | one => rfl
  | gen g => rfl
  | mul u v ihu ihv => rw [PWord.evalFin_mul, PWord.evalFin_mul, ihu, ihv]
  | inv u ih => rw [PWord.evalFin_inv, PWord.evalFin_inv, ih]
  | conj u g ihu ihg => rw [PWord.evalFin_conj, PWord.evalFin_conj, ihu, ihg]
  | comm u v ihu ihv => rw [PWord.evalFin_comm, PWord.evalFin_comm, ihu, ihv]
  | zpow u k ih => rw [PWord.evalFin_zpow, PWord.evalFin_zpow, ih]
  | z2pow u z ih => rw [PWord.evalFin_z2pow, PWord.evalFin_z2pow, ih]; exact key _ (hE₂ z)
  | profPow u γ ih =>
      by_cases hγ : γ = omega2
      · subst hγ
        rw [PWord.evalFin_profPow_omega2, PWord.evalFin_profPow_omega2, ih]
      · rw [PWord.evalFin_profPow_of_ne _ _ _ _ hγ, PWord.evalFin_profPow_of_ne _ _ _ _ hγ, ih]
        exact key _ (hE γ hγ)

end Resolver

section ResolverFox

variable {X : Type*} {C : Type*} [Group C] {A : Type*} [AddCommGroup A] [DistribMulAction C A]

/-- **Resolver correctness for the Fox evaluation, at the lift level** (the binding WW1
rule, packaged): over an elementary coefficient module, two resolver pairs agreeing modulo
`2 · N` — `N` any uniform bound on the base orders, e.g. `Monoid.exponent C` or
`Nat.card C` — give the same Fox evaluation of every word.  The factor `2` is the lift
level (`WordLift.pow_eq_pow_of_modEq_two_mul`): agreement modulo `N` alone silently halves
the level and produces the falsely-zero derivative. -/
theorem foxEval_resolver_congr (hA₂ : ∀ a : A, a + a = 0) {N : ℕ}
    (hbase : ∀ g : C, orderOf g ∣ N) (t : X → C) (a : X → A) {E E' : Zhat → ℤ}
    {E₂ E₂' : ℤ_[2] → ℤ} (hE : ∀ γ : Zhat, γ ≠ omega2 → E γ ≡ E' γ [ZMOD 2 * N])
    (hE₂ : ∀ z : ℤ_[2], E₂ z ≡ E₂' z [ZMOD 2 * N]) (w : PWord X) :
    foxEval t a E E₂ w = foxEval t a E' E₂' w :=
  PWord.evalFin_congr_of_orderOf_dvd
    (fun p => WordLift.orderOf_dvd_two_mul hA₂ hbase p) (foxLift t a) hE hE₂ w

/-- Resolver correctness for the Fox derivative. -/
theorem foxD_resolver_congr (hA₂ : ∀ a : A, a + a = 0) {N : ℕ}
    (hbase : ∀ g : C, orderOf g ∣ N) (t : X → C) (a : X → A) {E E' : Zhat → ℤ}
    {E₂ E₂' : ℤ_[2] → ℤ} (hE : ∀ γ : Zhat, γ ≠ omega2 → E γ ≡ E' γ [ZMOD 2 * N])
    (hE₂ : ∀ z : ℤ_[2], E₂ z ≡ E₂' z [ZMOD 2 * N]) (w : PWord X) :
    foxD t a E E₂ w = foxD t a E' E₂' w :=
  congrArg WordLift.u (foxEval_resolver_congr hA₂ hbase t a hE hE₂ w)

variable [Finite A] [Finite C]

/-- Resolver correctness for the evaluated two-relator Jacobian.  (The coefficient module is
pinned explicitly — the `(A := …)` discipline for statements equating two `foxJacobian`s.) -/
theorem foxJacobian_resolver_congr (hA₂ : ∀ a : A, a + a = 0) {N : ℕ}
    (hbase : ∀ g : C, orderOf g ∣ N) (t : X → C) {E E' : Zhat → ℤ} {E₂ E₂' : ℤ_[2] → ℤ}
    (hE : ∀ γ : Zhat, γ ≠ omega2 → E γ ≡ E' γ [ZMOD 2 * N])
    (hE₂ : ∀ z : ℤ_[2], E₂ z ≡ E₂' z [ZMOD 2 * N]) (R₁ R₂ : PWord X) :
    foxJacobian (A := A) t E E₂ R₁ R₂ = foxJacobian (A := A) t E' E₂' R₁ R₂ := by
  refine AddMonoidHom.ext fun a => ?_
  rw [foxJacobian_apply, foxJacobian_apply, foxD_resolver_congr hA₂ hbase t a hE hE₂ R₁,
    foxD_resolver_congr hA₂ hbase t a hE hE₂ R₂]

end ResolverFox

/-! ## Regression (mandatory, board WW2): the `Γ_R` row through full certificates

The recommended end-to-end target: WW1's `foxD_gammaRWildWord_split` row `x₁ + (1 + S⁻¹)x₂`,
certified to its published normal form — and past it, to the `τ`-pivot standard row by one
explicit column transvection — at **every** split simple tame module, plus the ramified twin.
Nothing below is cited by a proof. -/

section Regression

variable {C : Type*} [Group C] {V : Type*} [AddCommGroup V] [DistribMulAction C V]
variable [Finite C] [Finite V]

/-- The formal coefficient `1 + S⁻¹` of the published `Γ_R` row. -/
def oneAddSInv : FoxCoeff (TameSym 1) := .add .one (.atom (.gen .sigma (-1)))

/-- **The published `Γ_R` split row** `(0, 1, 1 + S⁻¹, 0)` in the packet's column order
`σ, τ, x₀, x₁` — the normal-form target of the published-row certificate.  Per the frozen
selection (`selection-freeze.md` row 1, SQ1) this is also the `L_sq` base-case row. -/
def gammaRSplitRow : FoxRowNormalForm (Generator 1) (TameSym 1) :=
  ⟨fun g => match g with
    | .sigma => .zero
    | .tau => .one
    | .wild i => if i = 0 then oneAddSInv else .zero⟩

@[simp] theorem gammaRSplitRow_sigma : gammaRSplitRow.row .sigma = .zero := rfl
@[simp] theorem gammaRSplitRow_tau : gammaRSplitRow.row .tau = .one := rfl
@[simp] theorem gammaRSplitRow_wild_zero : gammaRSplitRow.row (.wild 0) = oneAddSInv := rfl
@[simp] theorem gammaRSplitRow_wild_one : gammaRSplitRow.row (.wild 1) = .zero := rfl

/-- **The published `Γ_R` ramified row** `(0, 0, S⁻¹, 0)`. -/
def gammaRRamifiedRow : FoxRowNormalForm (Generator 1) (TameSym 1) :=
  ⟨fun g => match g with
    | .sigma => .zero
    | .tau => .zero
    | .wild i => if i = 0 then .atom (.gen .sigma (-1)) else .zero⟩

@[simp] theorem gammaRRamifiedRow_sigma : gammaRRamifiedRow.row .sigma = .zero := rfl
@[simp] theorem gammaRRamifiedRow_tau : gammaRRamifiedRow.row .tau = .zero := rfl
@[simp] theorem gammaRRamifiedRow_wild_zero :
    gammaRRamifiedRow.row (.wild 0) = .atom (.gen .sigma (-1)) := rfl
@[simp] theorem gammaRRamifiedRow_wild_one : gammaRRamifiedRow.row (.wild 1) = .zero := rfl

/-- **REGRESSION (mandatory, board WW2): the published-row certificate for the `Γ_R` wild
row**, at every split simple tame module: empty ops, target = the frozen row
`(0, 1, 1 + S⁻¹, 0)` under the split interpretation.  The `verifies` field is WW1's hand-row
identity restated at the certificate carrier `foxDHom` — replay is `rfl`, the `ω₂`-collapse
is inside the hand row. -/
noncomputable def gammaRWildRowCert (t : _root_.GQ2.Marking C) (hV₂ : ∀ v : V, v + v = 0)
    (hx0 : ∀ v : V, t.x₀ • v = v) (hx1 : ∀ v : V, t.x₁ • v = v) (htau : ∀ v : V, t.τ • v = v)
    (E : Zhat → ℤ) (E₂ : ℤ_[2] → ℤ) :
    FoxRowCertificate (TameSym.splitEnd (A := V) (Marking.ofQ2 t))
      (foxDHom (⇑(Marking.ofQ2 t)) E E₂ gammaRWildWord) where
  colOps := []
  target := gammaRSplitRow
  colOps_invertible := by simp
  verifies := by
    refine AddMonoidHom.ext fun a => ?_
    rw [foxRowApplyOps_nil, foxDHom_apply,
      foxD_gammaRWildWord_split_apply t hV₂ hx0 hx1 htau E E₂ a,
      FoxRowNormalForm.toHom_apply, sum_generator_one]
    simp only [gammaRSplitRow_sigma, gammaRSplitRow_tau, gammaRSplitRow_wild_zero,
      gammaRSplitRow_wild_one, oneAddSInv, FoxCoeff.eval_zero_apply, FoxCoeff.eval_one_apply,
      FoxCoeff.eval_add_apply, FoxCoeff.eval_atom_apply, TameSym.toEnd_gen_apply,
      Marking.apply_sigma, Marking.ofQ2_σ, zpow_neg, zpow_one, zero_add, add_zero]
    abel

/-- The explicit-ops list of the pivot certificate: one column transvection clearing the
`x₀`-column against the `τ`-pivot (`c_{x₀} ↦ c_{x₀} + c_τ ∘ (−(1 + S⁻¹)) = 0`). -/
def gammaRPivotOps : List (FoxColOp (Generator 1) (TameSym 1)) :=
  [.transvect .tau (.wild 0) (.neg oneAddSInv)]

/-- **REGRESSION (board WW2, the explicit-ops replay): the pivot certificate for the `Γ_R`
wild row**, at every split simple tame module: the single transvection of `gammaRPivotOps`
carries the published row to the standard `τ`-pivot row `(0, 1, 0, 0)`.  Replay is the
`rfl`-level `foxRowApplyOps` step plus the hand-row collapse — the ops algebra itself closes
by `abel`, no characteristic assumption. -/
noncomputable def gammaRWildRowPivotCert (t : _root_.GQ2.Marking C)
    (hV₂ : ∀ v : V, v + v = 0) (hx0 : ∀ v : V, t.x₀ • v = v) (hx1 : ∀ v : V, t.x₁ • v = v)
    (htau : ∀ v : V, t.τ • v = v) (E : Zhat → ℤ) (E₂ : ℤ_[2] → ℤ) :
    FoxRowCertificate (TameSym.splitEnd (A := V) (Marking.ofQ2 t))
      (foxDHom (⇑(Marking.ofQ2 t)) E E₂ gammaRWildWord) where
  colOps := gammaRPivotOps
  target := .single .tau
  colOps_invertible := by
    intro c hc
    rw [gammaRPivotOps, List.mem_singleton] at hc
    subst hc
    exact (by decide : (Generator.tau : Generator 1) ≠ .wild 0)
  verifies := by
    refine AddMonoidHom.ext fun a => ?_
    rw [foxRowApplyOps_apply, foxDHom_apply, gammaRPivotOps, FoxColOp.listHom_cons,
      FoxColOp.listHom_nil, AddMonoidHom.comp_apply, AddMonoidHom.id_apply,
      foxD_gammaRWildWord_split_apply t hV₂ hx0 hx1 htau E E₂ _,
      FoxRowNormalForm.single_toHom_apply]
    simp only [FoxColOp.toHom_transvect_apply, reduceIte, oneAddSInv, FoxCoeff.eval_neg_apply,
      FoxCoeff.eval_add_apply, FoxCoeff.eval_one_apply, FoxCoeff.eval_atom_apply,
      TameSym.toEnd_gen_apply, Marking.apply_sigma, Marking.ofQ2_σ, zpow_neg, zpow_one]
    abel

/-- **REGRESSION (the ramified twin): the published-row certificate for the ramified `Γ_R`
row**, at every ramified simple module (`V^T = 0`): empty ops, target `(0, 0, S⁻¹, 0)` under
the ramified interpretation (`P ↦ 0`) — mirroring the ℚ₂ split/ramified row pairs. -/
noncomputable def gammaRWildRowRamifiedCert (t : _root_.GQ2.Marking C)
    (hV₂ : ∀ v : V, v + v = 0) (hx0 : ∀ v : V, t.x₀ • v = v) (hx1 : ∀ v : V, t.x₁ • v = v)
    (htau : ∀ v : V, t.τ • v = v → v = 0) (hTodd : ∀ v : V, powOmega2 t.τ • v = v)
    (E : Zhat → ℤ) (E₂ : ℤ_[2] → ℤ) :
    FoxRowCertificate (TameSym.ramifiedEnd (A := V) (Marking.ofQ2 t))
      (foxDHom (⇑(Marking.ofQ2 t)) E E₂ gammaRWildWord) where
  colOps := []
  target := gammaRRamifiedRow
  colOps_invertible := by simp
  verifies := by
    refine AddMonoidHom.ext fun a => ?_
    rw [foxRowApplyOps_nil, foxDHom_apply,
      foxD_gammaRWildWord_ramified_apply t hV₂ hx0 hx1 htau hTodd E E₂ a,
      FoxRowNormalForm.toHom_apply, sum_generator_one]
    have hz : ∀ v : V, (0 : AddMonoid.End V) v = 0 := fun _ => rfl
    simp only [gammaRRamifiedRow_sigma, gammaRRamifiedRow_tau, gammaRRamifiedRow_wild_zero,
      gammaRRamifiedRow_wild_one, FoxCoeff.eval_zero, FoxCoeff.eval_atom, hz,
      TameSym.toEnd_gen_apply, Marking.apply_sigma, Marking.ofQ2_σ, zpow_neg, zpow_one,
      zero_add, add_zero]

end Regression

/-! ## Kernel-checkable instance verification (`decide`)

A full two-row certificate over a concrete module, closed by kernel `decide`: source matrix
rows `(1, s)` and `(0, 1)` over the two-slot alphabet `Bool`, coefficients in
`ZMod 2 × ZMod 2` with the atom `s` interpreted as the coordinate flip, one row swap plus
one column transvection, target the standard rows `(0, 1)`/`(1, 0)`.  This is the
"kernel-checkable verification on module instances" clause of the WW2 spec, exercised on the
ops/target algebra (a `foxDHom` instance is not `decide`-able past an `ω₂`-node — that
collapse routes through the engine lemmas, as in the regression above). -/

section DecideDemo

/-- The coordinate flip on `ZMod 2 × ZMod 2` — a nontrivial computable operator atom. -/
def demoFlip : AddMonoid.End (ZMod 2 × ZMod 2) :=
  AddMonoidHom.mk' (fun p => (p.2, p.1)) fun _ _ => rfl

/-- The demo interpretation: the unique atom is the coordinate flip. -/
def demoRho : Unit → AddMonoid.End (ZMod 2 × ZMod 2) := fun _ => demoFlip

/-- The demo source matrix: rows `(1, s)` and `(0, 1)` over the two-slot alphabet `Bool`. -/
def demoSource : FoxNormalForm Bool Unit :=
  ⟨⟨fun b => if b then .atom () else .one⟩, ⟨fun b => if b then .one else .zero⟩⟩

set_option maxRecDepth 4000 in
/-- **Kernel-`decide` certificate on a module instance** (board WW2): one row swap plus one
column transvection (clearing the `s`-entry against the first-slot pivot) carry `demoSource`
to the standard rows; `verifies` is closed by `decide` — the replay, the coefficient
evaluation and the normal-form sums all kernel-reduce. -/
def demoCert : FoxCertificate demoRho (demoSource.toHom demoRho) where
  rowOps := [.swap]
  colOps := [.transvect false true (.neg (.atom ()))]
  target := ⟨.single true, .single false⟩
  rowOps_invertible := by
    intro r hr
    rw [List.mem_singleton] at hr
    subst hr
    trivial
  colOps_invertible := by
    intro c hc
    rw [List.mem_singleton] at hc
    subst hc
    exact (by decide : false ≠ true)
  verifies := by
    have h : ∀ a : Bool → ZMod 2 × ZMod 2,
        foxApplyOps demoRho [.swap] [.transvect false true (.neg (.atom ()))]
            (demoSource.toHom demoRho) a
          = (FoxNormalForm.mk (.single true) (.single false)).toHom demoRho a := by decide
    exact AddMonoidHom.ext h

end DecideDemo

end GQ2.Dyadic
