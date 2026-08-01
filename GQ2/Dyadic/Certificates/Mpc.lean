/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Fable-5
-/
import GQ2.Dyadic.Certificates.MpcFox
import GQ2.Dyadic.Certificates.M0
import GQ2.Dyadic.Word.Hessian

/-!
# Dyadic campaign, ticket WMP-c: the procyclic `M_α` closer

The last certificate file of wave 2, sitting on WMP-b's Fox layer
(`GQ2/Dyadic/Certificates/MpcFox.lean`), WW3's Stokes/jet calculus
(`GQ2/Dyadic/Word/Stokes.lean`) and WW4's Hessian/phase interface
(`GQ2/Dyadic/Word/{Hessian,Phase}.lean`).  It carries **row 5 of the R5 selection freeze**,

```
R_{M,pc} = R_lin^pc · R̂^pc · D₀²[D₀,D₁] · H_h,     R̂^pc = Sh_M(R_lin^pc)
R_lin^pc = A²[A,B] · C₀^{2^α}[C₀,D] · E₀₁^pc · E₂^pc
C₀ = x₂σ₂^s,  A = x₀⁻¹C₀^{-m},  B = x₁σ₂^p,  D = σ^{η̂},  Ĉ₀ = σ₂^s
```

and the five items WMP-b handed over, in its order.

## §1 `hlin` — the linear copy acts trivially (handoff item 4)

WMP-b's `foxColumn_sigma_mul_eq_zero` carries `hlin` as an **explicit hypothesis**: the linear
copy's *value* acts trivially on the coefficient module.  It is discharged here, once, as
`trivAct_mpcLinW`, and the route is packet Prop. 9.2 read at the value level rather than at the
level of exponents:

* `A²` acts as `S₂^{−2sm}` and `C₀^{2^α}` as `S₂^{s·2^α}`, and `s·2^α = 2·(s·m)` (WMP-a's
  `s_mul_two_pow`) — so the two σ-skeletons cancel;
* `[A,B]` and `[C₀,D]` act trivially because **all four entries act as powers of one procyclic
  letter** — `S₂ = σ^{ω₂}` and `D`'s value `σ^n` (WMP-b's `exists_zpow_evalFin_etaDisplay`)
  commute, so the commutators are invisible to the module;
* `E₀₁^pc` and `E₂^pc` act trivially outright: every letter in them is a `δ`, and the `δ`-row
  acts trivially at the ramified reading (`trivAct_dW_ram`), while conjugation preserves that
  (`trivAct_conjR`).

The intermediate notion is `ActsAsPow`, a one-field predicate with the obvious closure calculus
(`mul`, `inv`, `zpow`, `commR`).  It is lane-generic — **nothing in it mentions this word** —
so the hoist WMP-b asked for is a cut-and-paste into `GQ2/Dyadic/Word/Fox.lean` beside WWH's
`trivAct` kit.  The Stokes lane needs the same fact and takes it from the same lemma.

## §2 The product certificate and the `√−10` instance (handoff item 1)

WMP-b deliberately deferred the WW2 records, and the reason is a finding: the hat copy's honest
first-order statement is **split by column**, so no single `FoxRowNormalForm` describes it.  The
object that *does* have a normal form is the **pair**, and that is what AS3 needs.  Assembled
here as

```
foxDHom (R_lin^pc · R̂^pc)  =  foxDHom (R_lin^pc) ∘ (kill the σ-coordinate)
```

(`foxD_mpcProductW_eq_lin`, and `foxDHom_mpcProductW_eq` for the carrier), from exactly two
WMP-b inputs and nothing else: MpcFox §5's `foxD_mpcHatW_ram` (the hat's wild and tame columns
vanish) and MpcFox §4's `foxColumn_sigma_mul_eq_zero` (the pair's σ-column vanishes, by the
coincidence, without either factor vanishing).  Both of those are **unconditional here**, since
`hlin` is discharged in §1.

⚠ **The certificate itself is a transport, and that is deliberate.**  `mpcProductRowCert`
produces a `FoxRowCertificate` for the pair from the linear copy's row **at σ-free offsets**
(`hlinrow`) together with a target whose σ-entry is `.zero`.  The linear copy's closed-form row
at general `(α, r, p)` — in particular the Fox row of the orbit-norm block `E₂^pc` — is a
`-b`-shaped computation that WMP-b did not do and this ticket does not own.  What *is* proved is
that the transport is sound and that its two hypotheses are exactly the shape the freeze already
uses: **both sibling lanes' frozen rows carry `.sigma => .zero`** (`MCompact.mCompactWildRow`,
`Npc.npcWildRow`), and neither copy of this row has an available σ-entry — which is precisely
the entry the pair kills.  The `√−10` instance `sqrtNeg10ProductRowCert` is the
`(α,r,p,η,h) = (2,1,1,.one,0)` specialization; the tree pin is `sqrtNeg10_gate9_hash` and the
tie to the frozen word is `eval_sqrtNeg10_factored`.

## §3 Self-replication cancellation, including every `T`-dependent central term (item 2)

Draft Rem. 5.4's second-order half.  Three things had to meet:

1. the **cross term** — `heisEvalZ_pair_z_of_hat_jetZero`, WMP-b's ready killer, consuming the
   *primal* half `p.a = 0`.  Wired to this word as `heisEvalZ_mpcProductW_z`; note that `T`
   enters only through `val(R_lin^pc)`, which in the cross term multiplies zero, so **no
   `T`-dependent central term can survive** and none has to be computed.
2. the **dual jet** `p.l = 0` for the hat copy — WMP-b delivered only the primal half, and WW3's
   `heisJetZero_mul_z` consumes only `.l`, so neither half alone gives the membership.  Proved
   here as `foxD_mpcHatW_ram_dual`, and it is **not a re-derivation**: `foxD_mpcHatW_ram` is
   module-generic, so the dual jet is that same theorem at `A := ElemDual V`.  What that costs
   is transferring the four ramified hypotheses to the dual module, three of which are immediate
   and one of which has content — `elemDual_fpf`: over a finite `V` an injective `τ − 1` is
   surjective, so a `τ`-invariant functional is killed by everything.  The membership is
   `heisJetZero_mpcHatW`.
   The two registers are joined by `heisEvalZ_a_eq_foxD`/`heisEvalZ_l_eq_foxD` under
   `ResolverLifts` — WW3's denotation is `evalZ` (resolver-driven) while WW1's is `evalFin`
   (which reads `ω₂` intrinsically), and `ResolverLifts` names the standing "resolvers correct
   at the lift level" discipline that makes them agree.  It is a **hypothesis**, and it is the
   only thing separating the two registers.
3. **P4's central clause**, which is a *module hypothesis*, not something to re-measure.  The
   shadow memo is explicit ("P4's hypothesis is a module condition, checked exactly per module
   here"), and its own table shows the clause **failing** on three of the four ramified simples
   while the conclusion still holds, because the memo's parity escape fires instead.  So the
   honest Lean shape is a named hypothesis with the memo's own two independent sufficient
   conditions, not a claim: `CentralReplication` is the clause and `mpcCopiesCancel` is the
   char-2 conclusion from it.  ⚠ The parity escape (`shadow_occurrence_parity`: a square
   contributes 2, a commutator 2+2, a conjugator 2, so the `A²[A,B]` shape both `M` rows are
   built from has both parities `0`) is **recorded as memo prose only** — it is not built here,
   because a Lean occurrence count needs an abelianized letter-multiset the `PWord` layer does
   not carry.

## §4 `affinePhase` (item 3) and the S4.5 block-order rider

`affinePhase` stays a **certificate input** — SD1 §6.3's row-5 satisfiability constraint is
binding, and the fields must be instantiable from the frozen row's endpoint polynomial, a CoV
`LinearEquiv` with inverse witness, and per-χ shift vectors, with nothing presupposing the
WC-Mpc analysis.  What this ticket adds against WW4's six-item gap list:

* item 4 (the σ-column coincidence lemma) — already banked by WMP-b;
* item 3's shadow half — **`mpcShadow_no_affine_shift`**, the corollary WW4 named but left
  unwritten, in WW4's own stated form (against `heisJetZero`, via `heisJetZero_mul_right_jet`),
  now applied to *this* word's hat copy rather than to an abstract jet-zero factor;
* items 1, 2, 6 — the endpoint polynomial and its CoV, **constructed**: the plus block
  `D₀²[D₀,D₁]` is what survives the cancellation and its word value is
  `Q₊(c₀,c₁) = q(c₀) + b_q(c₀,c₁)` (a word identity, not finite-order interpolation), which *is*
  a `plusFormD` endpoint — so `mpcPhaseCover` and `mpcHessianCertificate` are built from WW4's
  `plusFormDPhaseCover` with `LinearEquiv.refl` as the CoV (its inverse witness built into the
  structure).  Item 6 is honoured by **shape**: the diagonal is the abstract κ⁰ datum `d₀`, not
  the compact rows' `fun v ↦ dat.f v v`, because on the four refinement-free `P = 0` modules the
  datum is `TwistedClass2Domain`-normalized; `nonsingular_plusFormD` does not see `d₀`, so the
  twist cannot break nonsingularity (`mpcHessianCertificate_gaussSum`);
* item 3's shift vectors themselves — **remain an input** (they are per-χ field data, AS1's);
  only the shadow half is discharged;
* item 5 (the word-side `hessRelZ` equation at the graph marking) — **remains an input.**  It is
  the `npc_cross_operators` analogue and needs the NpcJet↔WordCoh bridge, which is wave-2 scope
  that no ticket owns.  `HessRelZTarget` names what it would have to say, and the file does not
  pretend to it.

**S4.5 rider (i)** — the block-order statement is a **gate-D statement, not a Hessian one**,
because `E₂^pc`'s second-order content is empty on the gate-E marking.  Formalized as
`swapDifference_zero_of_no_primal_x2` in WM0-c's `swapDifference_formula` shape: the offset of
the `E₂^pc` slot is `𝒪·(1+P)c₂`, and on the gate-E marking `c₂ = 0`.  **Rider (ii) is visible
in the statement**: the hypothesis is literally `c₂ = 0`, i.e. the x₂-has-no-primal-letter
convention, so a marking that gave the boundary generator a primal coordinate would not satisfy
it and block order would become load-bearing again — exactly as the decision note says.

## §5 The `E₀₁^pc` epistemics (item 5) — labelled exactly

Freeze row 5: `E₂^pc` is first-order essential, **`E₀₁^pc` is first-order redundant**, and its
justification is **second-order only** — the exact gate-F refutation on the fifth-root module.
Three statements, three different epistemic statuses, and this file keeps them apart:

| status | what | where |
|---|---|---|
| **theorem, here** | the block and its shadow copy contribute **zero** to the pair's Fox row, so gate D is silent about `E₀₁^pc` | `foxD_e01_pair_eq_zero` |
| **theorem, here** | the block-order difference vanishes on the gate-E marking (S4.5) | `swapDifference_zero_of_no_primal_x2` |
| **NOT proved here; cited** | the *positive* justification — gate F fails on the fifth-root module without `E₀₁^pc` | S4.4 measurement, freeze row 5; shape named by `E01SecondOrderWitness` |

⚠ The third row is a **measurement, not a Lean theorem**, and this file does not overclaim it.
S4.4's finding is that dropping the block passes gates A–E-scalar and dies at gate F; gate F is
a `𝔽₁₆`-module computation on the fifth root, and the Lean statement that would carry it is a
`decide` over a 16-element module's *second*-order data, which is a different object from
anything WMP-b or this ticket built.  What is recorded here is the **shape of the claim**
(`E01SecondOrderWitness`) and the theorem that gate D is silent, which is the half that makes
the citation necessary rather than optional.

## Implementation notes

**Not `module`-style, and forced**: `GQ2.Dyadic.Certificates.MpcFox` is plain-import (it
imports `Words/Mpc.lean`, which imports F3's `TameBoundary`), and a `module` file may not
import a non-`module` one — the WN0-a ruling that `Words/` and `Certificates/` are plain-import
layers.

**Reused, not re-derived** (WM0-c/WN0-c toolkit, cited by name): `MCompact.foxD_prodList_pair`,
`MCompact.evalFin_prodList_pair`, `MCompact.evalFin_sigma2W`, `MCompact.trivAct_commR_right`,
`Certificates.neg_eq_self`, WW3's `heisJetZero` family and `heisEvalZ_*` denotation API, WW4's
`hessSlice` calculus, `plusFormD` engine and `HessianCertificate`/`PhaseCoverCertificate`
records, and WM0-c's `swapDifference_formula`/`hessSlice_rev4_fib`.

**Hoist candidates** (beside WMP-b's seven): `ActsAsPow` with its seven closure lemmas,
`sigmaKill`/`pi_single_add_sigmaKill`/`foxRowNormalForm_toHom_sigmaKill`, `ResolverLifts` with
`evalZ_eq_evalFin_of_resolverLifts`, `heisPrimal`/`heisDual` with the two bridge lemmas (this is
the WW1↔WW3 bridge WW3's log promised as "one `map_evalZ` line" — it is that line, plus the
resolver hypothesis the promise omitted), `elemDual_smul_eq_self`/`elemDual_fpf`, and
`swapDifference_two_formula`.  None of them mentions this word.

**Axiom state.**  Every named declaration of this file depends on a subset of
`[propext, Classical.choice, Quot.sound]` (scratch audit over the full declaration list; not
committed).  Zero `sorryAx`, zero `native_decide`, and **no `decide` at all** — this row needed
no orbit pin, so the kernel-`decide` budget was never drawn on.  The census is untouched at
eleven.

**Headlines** (the audit surface): `trivAct_mpcLinW`, `foxD_mpcProductW_eq_lin`,
`foxDHom_mpcProductW_eq`, `mpcProductRowCert`, `sqrtNeg10ProductRowCert`,
`eval_sqrtNeg10_factored`, `foxD_mpcHatW_ram_dual`, `heisJetZero_mpcHatW`,
`heisEvalZ_mpcProductW_z`, `mpcCopiesCancel`, `mpcShadow_no_affine_shift`, `mpcPhaseCover`,
`mpcHessianCertificate`, `swapDifference_zero_of_no_primal_x2`, `foxD_e01_pair_eq_zero`.
-/

namespace GQ2.Dyadic.Certificates.MProcyclic

open GQ2.FoxH GQ2.Dyadic.Words GQ2.Dyadic.Words.Mpc

open GQ2.Dyadic.Words.MCompact renaming deltaC → deltaCert

/-! ## §1 `ActsAsPow` — the value-level Prop. 9.2 balance

Lane-generic.  The predicate says a group element acts on the coefficient module exactly as a
fixed integer power of one distinguished element `U`; the closure calculus below is everything
the procyclic row needs, and `commR` is the interesting clause — two elements acting as powers
of a *common* `U` have a commutator that the module cannot see, whatever the elements
themselves do. -/

section ActsAsPow

variable {C : Type*} [Group C] {V : Type*} [AddCommGroup V] [DistribMulAction C V]

/-- `x` acts on `V` exactly as `U ^ k`. -/
def ActsAsPow (U : C) (k : ℤ) (x : C) (V : Type*) [AddCommGroup V] [DistribMulAction C V] :
    Prop :=
  ∀ v : V, x • v = (U ^ k) • v

theorem actsAsPow_one (U : C) : ActsAsPow U 0 (1 : C) V := by
  intro v; rw [zpow_zero]

theorem ActsAsPow.mul {U x y : C} {i j : ℤ} (hx : ActsAsPow U i x V)
    (hy : ActsAsPow U j y V) : ActsAsPow U (i + j) (x * y) V := by
  intro v
  rw [mul_smul, hy v, hx _, ← mul_smul, ← zpow_add]

theorem ActsAsPow.inv {U x : C} {i : ℤ} (hx : ActsAsPow U i x V) :
    ActsAsPow U (-i) x⁻¹ V := by
  intro v
  have h : x • ((U ^ (-i)) • v) = v := by
    rw [hx, ← mul_smul, ← zpow_add, add_neg_cancel, zpow_zero, one_smul]
  exact inv_smul_eq_iff.mpr h.symm

theorem ActsAsPow.zpow {U x : C} {i : ℤ} (hx : ActsAsPow U i x V) :
    ∀ k : ℤ, ActsAsPow U (k * i) (x ^ k) V := by
  have hnat : ∀ n : ℕ, ActsAsPow U ((n : ℤ) * i) (x ^ n) V := by
    intro n
    induction n with
    | zero => simpa using actsAsPow_one (V := V) U
    | succ n ih =>
        have h2 := ih.mul hx
        rw [← pow_succ] at h2
        have he : (n : ℤ) * i + i = ((n + 1 : ℕ) : ℤ) * i := by push_cast; ring
        rwa [he] at h2
  intro k
  cases k with
  | ofNat n => simpa [zpow_natCast] using hnat n
  | negSucc n =>
      have h3 := (hnat (n + 1)).inv
      have he : (Int.negSucc n) * i = -(((n + 1 : ℕ) : ℤ) * i) := by
        rw [Int.negSucc_eq, neg_mul]
        push_cast
        ring
      have hp : x ^ (Int.negSucc n) = (x ^ (n + 1))⁻¹ := zpow_negSucc x n
      rw [he, hp]
      exact h3

/-- **Commutators of two `U`-powers are invisible to the module.**  This is the clause that
makes `[A,B]` and `[C₀,D]` drop out of the linear copy's value: `A`, `B`, `C₀` all act as
powers of `S₂ = σ^{ω₂}`, and `D = σ^{η̂}` acts as a power of `σ` — hence of the same procyclic
letter — so the four actions commute even though the group elements need not. -/
theorem ActsAsPow.trivAct_commR {U x y : C} {i j : ℤ} (hx : ActsAsPow U i x V)
    (hy : ActsAsPow U j y V) : commR x y ∈ trivAct C V := by
  rw [mem_trivAct]
  intro v
  have h := ((hx.inv.mul hy.inv).mul (hx.mul hy)) v
  rw [show -i + -j + (i + j) = 0 by ring, zpow_zero, one_smul] at h
  have hg : commR x y = x⁻¹ * y⁻¹ * (x * y) := by
    show x⁻¹ * y⁻¹ * x * y = x⁻¹ * y⁻¹ * (x * y)
    group
  rwa [hg]

/-- An element acting as the zero power acts trivially. -/
theorem ActsAsPow.trivial_of_zero {U x : C} (hx : ActsAsPow U 0 x V) : x ∈ trivAct C V := by
  rw [mem_trivAct]
  intro v
  rw [hx v, zpow_zero, one_smul]

/-- A trivially-acting element acts as any power's worth of nothing: the zero power. -/
theorem ActsAsPow.of_trivial {U x : C} (hx : x ∈ trivAct C V) : ActsAsPow U 0 x V := by
  intro v
  rw [mem_trivAct.mp hx v, zpow_zero, one_smul]

/-- Rewriting the exponent. -/
theorem ActsAsPow.congr_exp {U x : C} {k k' : ℤ} (hk : k = k') (hx : ActsAsPow U k x V) :
    ActsAsPow U k' x V := by rw [← hk]; exact hx

/-- **Base change.**  Reading an `ActsAsPow` statement at a root of the base: this is what lets
the commutator clause fire on `[C₀, D]`, whose two entries are naturally read at *different*
bases (`S₂ = σ^{ω₂}` and `σ` itself). -/
theorem ActsAsPow.base_zpow {U W x : C} {k e : ℤ} (hU : U = W ^ e) (hx : ActsAsPow U k x V) :
    ActsAsPow W (e * k) x V := by
  intro v
  rw [hx v, hU, ← zpow_mul]

end ActsAsPow

/-! ## §1b `hlin` — the linear copy acts trivially

The discharge of WMP-b's explicit hypothesis, and the value-level face of packet Prop. 9.2.
Every declaration below is stated at general `(α, r, p, h)` and every `η̂` display. -/

section Hlin

variable {h : ℕ} {C : Type*} [Group C] [Finite C] {V : Type*} [AddCommGroup V] [Finite V]
  [DistribMulAction C V] (t : Marking (2 + 2 * h) C) (E : Zhat → ℤ) (E₂ : ℤ_[2] → ℤ)

omit [Finite C] [Finite V] in
/-- `S₂ = σ^{ω₂}` is an integer power of the procyclic letter `σ`. -/
theorem powOmega2_sigma_eq_zpow :
    powOmega2 t.σ = t.σ ^ ((omega2Exp (orderOf t.σ) : ℕ) : ℤ) := by
  rw [zpow_natCast]
  rfl

omit [Finite C] [Finite V] in
/-- The `x_i` letters act trivially, in **this lane's** spelling of `coreLetter`.

⚠ `Words.Mpc.coreLetter` and `Words.MCompact.coreLetter` are `rfl`-equal but not syntactically
identical, so the compact lane's lemma cannot be handed to `rw` directly — the restatement is
what makes the rewrite patterns match (WM0-c's `coreLetter_eq` gotcha, one level up). -/
theorem trivAct_coreLetterM (hwild : ∀ (i : Fin (2 + 2 * h + 1)) (v : V), t.x i • v = v)
    (i : Fin 3) : ⇑t (coreLetter h i) ∈ trivAct C V :=
  MCompact.trivAct_coreLetter t hwild i

omit [Finite C] [Finite V] in
/-- `C₀ = x₂σ₂^s` acts as `S₂^s`: the boundary letter is invisible, the tail is the balance. -/
theorem actsAsPow_c0W (hwild : ∀ (i : Fin (2 + 2 * h + 1)) (v : V), t.x i • v = v) (s' : ℕ) :
    ActsAsPow (powOmega2 t.σ) (s' : ℤ) (PWord.evalFin ⇑t E E₂ (c0W h s')) V := by
  intro v
  rw [c0W, MCompact.evalFin_prodList_pair, PWord.evalFin_gen, PWord.evalFin_zpow,
    MCompact.evalFin_sigma2W, mul_smul,
    mem_trivAct.mp (trivAct_coreLetterM t hwild 2)]

omit [Finite C] [Finite V] in
/-- `A = x₀⁻¹C₀^{−m}` acts as `S₂^{−sm}`. -/
theorem actsAsPow_aW (hwild : ∀ (i : Fin (2 + 2 * h + 1)) (v : V), t.x i • v = v) (s' mm : ℕ) :
    ActsAsPow (powOmega2 t.σ) (-(s' * mm : ℕ) : ℤ)
      (PWord.evalFin ⇑t E E₂ (aW h s' mm)) V := by
  refine ActsAsPow.congr_exp (k := 0 + (-(mm : ℤ)) * (s' : ℤ)) (by push_cast; ring) ?_
  rw [aW, MCompact.evalFin_prodList_pair, PWord.evalFin_zpow, PWord.evalFin_inv,
    PWord.evalFin_gen]
  exact ActsAsPow.mul
    (ActsAsPow.of_trivial (inv_mem (trivAct_coreLetterM t hwild 0)))
    ((actsAsPow_c0W t E E₂ hwild s').zpow _)

omit [Finite C] [Finite V] in
/-- `σ₂^k` in the emitter's two spellings acts as `S₂^k`. -/
theorem actsAsPow_sig2PowW : ∀ k : ℕ,
    ActsAsPow (powOmega2 t.σ) (k : ℤ)
      (PWord.evalFin ⇑t E E₂ (sig2PowW h k)) V
  | 0 => by
      intro v
      rw [show sig2PowW h 0 = .zpow sigma2W ((0 : ℕ) : ℤ) from rfl, PWord.evalFin_zpow,
        MCompact.evalFin_sigma2W]
  | 1 => by
      intro v
      rw [show sig2PowW h 1 = sigma2W from rfl, MCompact.evalFin_sigma2W]
      simp
  | k + 2 => by
      intro v
      rw [show sig2PowW h (k + 2) = .zpow sigma2W ((k + 2 : ℕ) : ℤ) from rfl,
        PWord.evalFin_zpow, MCompact.evalFin_sigma2W]

omit [Finite C] [Finite V] in
/-- `B = x₁σ₂^p` acts as `S₂^p` — and, unlike the compact row's bare `x₁`, **not** trivially.
That is exactly the difference WMP-b's §4 contrast records. -/
theorem actsAsPow_bW (hwild : ∀ (i : Fin (2 + 2 * h + 1)) (v : V), t.x i • v = v) :
    ∀ pp : ℕ, ActsAsPow (powOmega2 t.σ) (pp : ℤ) (PWord.evalFin ⇑t E E₂ (bW h pp)) V
  | 0 => by
      intro v
      rw [show bW h 0 = .gen (coreLetter h 1) from rfl, PWord.evalFin_gen,
        mem_trivAct.mp (trivAct_coreLetterM t hwild 1)]
      simp
  | q + 1 => by
      refine ActsAsPow.congr_exp (k := 0 + ((q + 1 : ℕ) : ℤ)) (by push_cast; ring) ?_
      rw [show bW h (q + 1) = PWord.prodList [.gen (coreLetter h 1), sig2PowW h (q + 1)] from rfl,
        MCompact.evalFin_prodList_pair, PWord.evalFin_gen]
      exact ActsAsPow.mul
        (ActsAsPow.of_trivial (trivAct_coreLetterM t hwild 1))
        (actsAsPow_sig2PowW t E E₂ (q + 1))

/-! ### The two 𝓔-blocks are invisible outright

`E₀₁^pc` and `E₂^pc` are words in `δ₀, δ₁, δ₂` and `σ₂`-conjugators alone, and every `σ₂`
occurrence in them is a **conjugator**.  So at the ramified reading — where the `δ`-row acts
trivially — the whole block acts trivially, with no balance and no characteristic hypothesis.
This is the value-level face of "`E₂^pc`'s second-order content is empty on the gate-E
marking". -/

section EBlocks

variable (hwild : ∀ (i : Fin (2 + 2 * h + 1)) (v : V), t.x i • v = v)
  (hTodd : ∀ v : V, powOmega2 t.τ • v = v)

include hwild hTodd

/-- The `𝓔₀₁`-block acts trivially. -/
theorem trivAct_e01W (aa bb : ℕ) :
    PWord.evalFin ⇑t E E₂ (e01W h aa bb) ∈ trivAct C V := by
  have hd : ∀ i : Fin 3, PWord.evalFin ⇑t E E₂ (dW h i) ∈ trivAct C V := fun i =>
    trivAct_dW_ram t E E₂ hwild hTodd i
  rw [e01W]
  refine trivAct_evalFin_prodList ?_
  intro w hw
  rcases List.mem_cons.mp hw with rfl | hw
  · rw [PWord.evalFin_conj]
    refine trivAct_conjR (trivAct_evalFin_prodList ?_) _
    intro u hu
    rcases List.mem_cons.mp hu with rfl | hu
    · rw [PWord.evalFin_conj]; exact trivAct_conjR (hd 1) _
    rcases List.mem_cons.mp hu with rfl | hu
    · exact hd 1
    rcases List.mem_cons.mp hu with rfl | hu
    · exact hd 0
    · simp at hu
  rcases List.mem_cons.mp hw with rfl | hw
  · exact hd 0
  · simp at hw

/-- The orbit-norm letter `z = δ₂δ₂^V` acts trivially, in both emitted spellings. -/
theorem trivAct_zW : ∀ pp : ℕ, PWord.evalFin ⇑t E E₂ (zW h pp) ∈ trivAct C V
  | 0 => by
      rw [show zW h 0 = .zpow (dW h 2) ((2 : ℕ) : ℤ) from rfl, PWord.evalFin_zpow]
      exact zpow_mem (trivAct_dW_ram t E E₂ hwild hTodd 2) _
  | q + 1 => by
      rw [show zW h (q + 1)
          = PWord.prodList [dW h 2, .conj (dW h 2) (sig2PowW h (q + 1))] from rfl]
      refine trivAct_evalFin_prodList ?_
      intro w hw
      rcases List.mem_cons.mp hw with rfl | hw
      · exact trivAct_dW_ram t E E₂ hwild hTodd 2
      rcases List.mem_cons.mp hw with rfl | hw
      · rw [PWord.evalFin_conj]
        exact trivAct_conjR (trivAct_dW_ram t E E₂ hwild hTodd 2) _
      · simp at hw

/-- The `𝓔₂`-block — orbit-norm node and all — acts trivially.  The orbit norm is a product of
`σ₂`-conjugates of one trivially-acting letter, so `S1.9`'s `orbitNorm_eq` is not needed at the
value level: normality of `trivAct` does all of it. -/
theorem trivAct_e2W (s' mm pp : ℕ) :
    PWord.evalFin ⇑t E E₂ (e2W h s' mm pp) ∈ trivAct C V := by
  rw [e2W]
  refine trivAct_evalFin_prodList ?_
  intro w hw
  rcases List.mem_cons.mp hw with rfl | hw
  · rw [PWord.evalFin_conj]
    exact trivAct_conjR (trivAct_dW_ram t E E₂ hwild hTodd 2) _
  rcases List.mem_cons.mp hw with rfl | hw
  · rw [PWord.evalFin_conj]
    refine trivAct_conjR (trivAct_evalFin_prodList ?_) _
    intro u hu
    rw [Export.orbitNormFactors, List.mem_map] at hu
    obtain ⟨j, -, rfl⟩ := hu
    rw [PWord.evalFin_conj]
    exact trivAct_conjR (trivAct_zW t E E₂ hwild hTodd pp) _
  · simp at hw

end EBlocks

/-! ### The assembled balance — `hlin`

WMP-b's explicit hypothesis, discharged. -/

/-- **`hlin`: the linear copy's value acts trivially** — packet Prop. 9.2 read at the value
level, at general `(α, r, p, h)` and every `η̂` display.

`A²` contributes `S₂^{−2sm}`, `C₀^{2^α}` contributes `S₂^{s·2^α}`, and `s·2^α = 2·(s·m)`
(WMP-a's `s_mul_two_pow`) makes them cancel; the two commutators are invisible because all four
entries act as powers of one procyclic letter; the two `𝓔`-blocks are invisible outright.

This is exactly the hypothesis `foxColumn_sigma_mul_eq_zero` carries, so the σ-column theorem
becomes unconditional in `α ≥ 1` (`foxColumn_sigma_mul_eq_zero'` below), and the Stokes lane
takes the same fact from here rather than re-deriving it. -/
theorem trivAct_mpcLinW {α : ℕ} (hα : 1 ≤ α) (r pp : ℕ) (η : EtaDisplay)
    (hwild : ∀ (i : Fin (2 + 2 * h + 1)) (v : V), t.x i • v = v)
    (hTodd : ∀ v : V, powOmega2 t.τ • v = v) :
    PWord.evalFin ⇑t E E₂ (mpcLinW α r pp η h) ∈ trivAct C V := by
  obtain ⟨n, hn⟩ := exists_zpow_evalFin_etaDisplay (h := h) t E E₂ η
  have hU : powOmega2 t.σ = t.σ ^ ((omega2Exp (orderOf t.σ) : ℕ) : ℤ) :=
    powOmega2_sigma_eq_zpow t
  have hbal : ((2 : ℕ) : ℤ) * (-(s r * m α : ℕ) : ℤ)
      + (0 + (((2 ^ α : ℕ) : ℤ) * (s r : ℤ) + (0 + (0 + (0 + 0))))) = 0 := by
    have := congrArg (fun k : ℕ => (k : ℤ)) (s_mul_two_pow hα r)
    push_cast at this ⊢
    linarith
  refine ActsAsPow.trivial_of_zero (U := powOmega2 t.σ) (ActsAsPow.congr_exp hbal ?_)
  rw [mpcLinW, linFactors]
  simp only [PWord.prodList_cons, PWord.prodList_nil, PWord.evalFin_mul, PWord.evalFin_one,
    PWord.evalFin_zpow, PWord.evalFin_comm]
  refine ActsAsPow.mul ((actsAsPow_aW t E E₂ hwild _ _).zpow _) (ActsAsPow.mul ?_
    (ActsAsPow.mul ((actsAsPow_c0W t E E₂ hwild _).zpow _) (ActsAsPow.mul ?_
      (ActsAsPow.mul (ActsAsPow.of_trivial (trivAct_e01W t E E₂ hwild hTodd _ _))
        (ActsAsPow.mul (ActsAsPow.of_trivial (trivAct_e2W t E E₂ hwild hTodd _ _ _))
          (actsAsPow_one _))))))
  · exact ActsAsPow.of_trivial
      ((actsAsPow_aW t E E₂ hwild _ _).trivAct_commR (actsAsPow_bW t E E₂ hwild _))
  · refine ActsAsPow.of_trivial (ActsAsPow.trivAct_commR (U := t.σ) (j := n)
      ((actsAsPow_c0W t E E₂ hwild (s r)).base_zpow hU) ?_)
    intro v
    rw [hn]

end Hlin

/-! ## §2 The product row and its WW2 certificate

WMP-b deferred the WW2 records for a structural reason: the hat copy's honest first-order
statement is split by column, so no single `FoxRowNormalForm` describes it.  The **pair** does
have one, and this section assembles it from exactly two inputs — §5's `foxD_mpcHatW_ram` and
§4's `foxColumn_sigma_mul_eq_zero`. -/

section Product

variable {h : ℕ} {C : Type*} [Group C] [Finite C] {V : Type*} [AddCommGroup V] [Finite V]
  [DistribMulAction C V] (t : Marking (2 + 2 * h) C) (E : Zhat → ℤ) (E₂ : ℤ_[2] → ℤ)

/-- **Killing the σ-coordinate of an offset vector.**  Lane-generic: a Fox row splits as its
σ-column plus its restriction to σ-free offsets, and on this row the two halves are proved by
two different engines, so the split has to be nameable. -/
def sigmaKill {n : ℕ} {A : Type*} [AddCommGroup A] (a : Generator n → A) : Generator n → A :=
  fun g => if g = Generator.sigma then 0 else a g

@[simp] theorem sigmaKill_sigma {n : ℕ} {A : Type*} [AddCommGroup A] (a : Generator n → A) :
    sigmaKill a Generator.sigma = 0 := by rw [sigmaKill, if_pos rfl]

theorem sigmaKill_of_ne {n : ℕ} {A : Type*} [AddCommGroup A] (a : Generator n → A)
    {g : Generator n} (hg : g ≠ Generator.sigma) : sigmaKill a g = a g := by
  rw [sigmaKill, if_neg hg]

/-- The offset vector is its σ-column plus its σ-free part. -/
theorem pi_single_add_sigmaKill {n : ℕ} {A : Type*} [AddCommGroup A] (a : Generator n → A) :
    Pi.single Generator.sigma (a Generator.sigma) + sigmaKill a = a := by
  funext g
  rcases eq_or_ne g Generator.sigma with rfl | hg
  · rw [Pi.add_apply, Pi.single_eq_same, sigmaKill_sigma, add_zero]
  · rw [Pi.add_apply, Pi.single_eq_of_ne hg, sigmaKill_of_ne a hg, zero_add]

/-- `σ`-column offsets are invisible to the `δ`-row: `δ_i` carries no `σ`. -/
theorem foxD_dW_sigma_single (hwild : ∀ (i : Fin (2 + 2 * h + 1)) (w : V), t.x i • w = w)
    (hτfpf : ∀ w : V, t.τ • w = w → w = 0) (hTodd : ∀ w : V, powOmega2 t.τ • w = w)
    (v : V) (i : Fin 3) :
    foxD ⇑t (Pi.single Generator.sigma v) E E₂ (dW h i) = 0 := by
  rw [foxD_dW_ram t E E₂ _ hwild hτfpf hTodd i,
    Pi.single_eq_of_ne (coreLetter_ne_sigma h i), neg_zero]

/-- **The pair's σ-column vanishes** — WMP-b's coincidence lemma, now unconditional: `hlin` is
`trivAct_mpcLinW` and the two `δ`-side hypotheses are the ramified reading. -/
theorem foxColumn_sigma_mpcProductW_eq_zero {α : ℕ} (hα : 1 ≤ α) (r pp : ℕ) (η : EtaDisplay)
    (hV₂ : ∀ w : V, w + w = 0)
    (hwild : ∀ (i : Fin (2 + 2 * h + 1)) (w : V), t.x i • w = w)
    (hτfpf : ∀ w : V, t.τ • w = w → w = 0) (hTodd : ∀ w : V, powOmega2 t.τ • w = w) :
    foxColumn (A := V) ⇑t E E₂ (.mul (mpcLinW α r pp η h) (mpcHatW α r pp η h))
        Generator.sigma = 0 :=
  foxColumn_sigma_mul_eq_zero t E E₂ α r pp η hV₂
    (trivAct_mpcLinW t E E₂ hα r pp η hwild hTodd) hwild
    (fun i => trivAct_dW_ram t E E₂ hwild hTodd i)
    (fun v i => foxD_dW_sigma_single t E E₂ hwild hτfpf hTodd v i)

/-- **The product row IS the linear row, read at σ-free offsets.**

The whole content of handoff item 1, in one equation and from exactly two WMP-b inputs:

* the σ-column dies by the **coincidence** (`foxColumn_sigma_mul_eq_zero`) — a statement about
  the *pair*, true although neither factor's σ-column vanishes;
* the wild and tame columns of the hat copy die by **Rem. 5.4** (`foxD_mpcHatW_ram`), so the
  σ-free part of the pair's row is the linear copy's outright — the hat contributes nothing,
  and the prefix weight `val(R_lin^pc)` never has to be computed because it multiplies zero.

⚠ The two halves are proved by different engines and the statement keeps them visible: the
right-hand side is the linear row at the **σ-killed** offset, not at `a`. -/
theorem foxD_mpcProductW_eq_lin {α : ℕ} (hα : 1 ≤ α) (r pp : ℕ) (η : EtaDisplay)
    (hV₂ : ∀ w : V, w + w = 0)
    (hwild : ∀ (i : Fin (2 + 2 * h + 1)) (w : V), t.x i • w = w)
    (hτfpf : ∀ w : V, t.τ • w = w → w = 0) (hTodd : ∀ w : V, powOmega2 t.τ • w = w)
    (a : Generator (2 + 2 * h) → V) :
    foxD ⇑t a E E₂ (.mul (mpcLinW α r pp η h) (mpcHatW α r pp η h))
      = foxD ⇑t (sigmaKill a) E E₂ (mpcLinW α r pp η h) := by
  have hcol := congrArg (fun f : V →+ V => f (a Generator.sigma))
    (foxColumn_sigma_mpcProductW_eq_zero t E E₂ hα r pp η hV₂ hwild hτfpf hTodd)
  simp only [foxColumn_apply, AddMonoidHom.zero_apply] at hcol
  conv_lhs => rw [← pi_single_add_sigmaKill a]
  rw [foxD_add, hcol, zero_add, foxD_mul,
    foxD_mpcHatW_ram t E E₂ (sigmaKill a) (sigmaKill_sigma a) hwild hτfpf hTodd hα r pp η hV₂,
    smul_zero, add_zero]

/-- The `AddMonoidHom` form: the pair's Fox carrier factors through the σ-killing projection. -/
theorem foxDHom_mpcProductW_eq {α : ℕ} (hα : 1 ≤ α) (r pp : ℕ) (η : EtaDisplay)
    (hV₂ : ∀ w : V, w + w = 0)
    (hwild : ∀ (i : Fin (2 + 2 * h + 1)) (w : V), t.x i • w = w)
    (hτfpf : ∀ w : V, t.τ • w = w → w = 0) (hTodd : ∀ w : V, powOmega2 t.τ • w = w) :
    foxDHom (A := V) ⇑t E E₂ (.mul (mpcLinW α r pp η h) (mpcHatW α r pp η h))
      = AddMonoidHom.mk' (fun a => foxD ⇑t (sigmaKill a) E E₂ (mpcLinW α r pp η h))
          (fun a b => by
            rw [show sigmaKill (a + b) = sigmaKill a + sigmaKill b by
              funext g; rcases eq_or_ne g Generator.sigma with rfl | hg
              · simp [sigmaKill]
              · simp [sigmaKill_of_ne _ hg]]
            exact foxD_add ⇑t E E₂ _ _ _) := by
  refine AddMonoidHom.ext fun a => ?_
  rw [foxDHom_apply, AddMonoidHom.mk'_apply]
  exact foxD_mpcProductW_eq_lin t E E₂ hα r pp η hV₂ hwild hτfpf hTodd a

/-! ### The WW2 row certificate

A `FoxRowNormalForm` whose σ-entry is `.zero` cannot see the σ-killing projection, so the pair's
certificate is the linear copy's σ-free row verbatim.  **Both sibling lanes' frozen rows already
have that shape** (`MCompact.mCompactWildRow` and `Npc.npcWildRow` both match `.sigma => .zero`),
which is what makes this the right transport rather than a convenience. -/

omit [Finite V] in
/-- A normal form with a zero σ-entry cannot see the σ-killing projection. -/
theorem foxRowNormalForm_toHom_sigmaKill {S : Type*} (ρ : S → AddMonoid.End V)
    (nf : FoxRowNormalForm (Generator (2 + 2 * h)) S)
    (hσ : nf.row Generator.sigma = .zero) (a : Generator (2 + 2 * h) → V) :
    nf.toHom ρ (sigmaKill a) = nf.toHom ρ a := by
  rw [FoxRowNormalForm.toHom_apply, FoxRowNormalForm.toHom_apply]
  refine Finset.sum_congr rfl fun g _ => ?_
  rcases eq_or_ne g Generator.sigma with rfl | hg
  · rw [hσ]
    simp
  · rw [sigmaKill_of_ne a hg]

/-- **The WW2 row certificate of the pair `R_lin^pc · R̂^pc`** — handoff item 1.

The input `hlinrow` is the linear copy's row **at σ-free offsets only**, which is exactly the
honest `-b` object: WMP-b never claimed a σ-entry for either copy, and the freeze's whole point
is that no such assertion is available.  What the pair buys is precisely the σ-entry: the
coincidence kills it, so a target with `.sigma => .zero` verifies.

⚠ This is a transport and says so.  The closed form of `hlinrow` at general `(α, r, p)` — in
particular the Fox row of the orbit-norm block `E₂^pc` — is a `-b`-shaped computation that
WMP-b did not do and this ticket does not own; it is named in the report as what AS3 still
owes.  Everything *around* it is unconditional. -/
noncomputable def mpcProductRowCert {S : Type*} (ρ : S → AddMonoid.End V)
    {α : ℕ} (hα : 1 ≤ α) (r pp : ℕ) (η : EtaDisplay) (hV₂ : ∀ w : V, w + w = 0)
    (hwild : ∀ (i : Fin (2 + 2 * h + 1)) (w : V), t.x i • w = w)
    (hτfpf : ∀ w : V, t.τ • w = w → w = 0) (hTodd : ∀ w : V, powOmega2 t.τ • w = w)
    (target : FoxRowNormalForm (Generator (2 + 2 * h)) S)
    (hσzero : target.row Generator.sigma = .zero)
    (hlinrow : ∀ a : Generator (2 + 2 * h) → V, a Generator.sigma = 0 →
      foxD ⇑t a E E₂ (mpcLinW α r pp η h) = target.toHom ρ a) :
    FoxRowCertificate ρ
      (foxDHom (A := V) ⇑t E E₂ (.mul (mpcLinW α r pp η h) (mpcHatW α r pp η h))) where
  colOps := []
  target := target
  colOps_invertible := by simp
  verifies := by
    refine AddMonoidHom.ext fun a => ?_
    rw [foxRowApplyOps_nil, foxDHom_apply,
      foxD_mpcProductW_eq_lin t E E₂ hα r pp η hV₂ hwild hτfpf hTodd a,
      hlinrow _ (sigmaKill_sigma a), foxRowNormalForm_toHom_sigmaKill ρ target hσzero a]

end Product

/-! ### The `ℚ₂(√−10)` instance — merge gate 9

`(r, ε, η) = (1, 1, 1)` (packet Cor. 8.2; the sign row does not exist), i.e.
`(α, r, p, η, h) = (2, 1, 1, .one, 0)`: `s = 2`, `m = 2`, `p = 1`, `2^α = 4`. -/

section SqrtNeg10

/-- The `√−10` **pair** word.  Not a syntactic slice of `mpcW` — `prodList` does not split over
`++` (WMP-a) — so the tie to the gate-9 tree is the value identity below. -/
noncomputable def sqrtNeg10ProductW : PWord (Generator 2) :=
  .mul (mpcLinW 2 1 1 .one 0) (mpcHatW 2 1 1 .one 0)

/-- **Merge gate 9, restated in the certificate layer**: the digest this lane's `√−10` row
carries is WMP-a's, which is WW5's `frozenRowHashes` entry, which is the selection freeze's. -/
theorem sqrtNeg10_gate9_hash :
    rawMpcSqrtNeg10_astHash
      = "55b24a4b141274bc30d09468096f4fa021184c5dc22c17823e423457928a26cf" := rfl

/-- The gate-9 tree denotes to the word this section factors. -/
theorem sqrtNeg10_denote :
    Export.denote (denoteCtx 0) rawMpcSqrtNeg10 = some (mpcW 2 1 1 .one 0) :=
  denote_rawMpc_sqrtNeg10

/-- **The `√−10` factorization**: the gate-9 word is the pair times the plus block times the
(empty, at `h = 0`) handle tail.  This is the value-level statement AS3 consumes — the pair is
where the certificate lives, and the plus block is what survives the cancellation. -/
theorem eval_sqrtNeg10_factored {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [TotallyDisconnectedSpace G] (t : Marking (2 + 2 * 0) G) :
    t.eval (mpcW 2 1 1 .one 0)
      = t.eval sqrtNeg10ProductW * t.eval (plusW 0) * t.eval (handlesW 0) := by
  rw [show sqrtNeg10ProductW = .mul (mpcLinW 2 1 1 .one 0) (mpcHatW 2 1 1 .one 0) from rfl,
    Marking.eval_mul, eval_mpcW_factored]

variable {C : Type*} [Group C] [Finite C] {V : Type*} [AddCommGroup V] [Finite V]
  [DistribMulAction C V] (t : Marking 2 C) (E : Zhat → ℤ) (E₂ : ℤ_[2] → ℤ)

/-- **AS3's entry point for merge gate 9**: the `√−10` pair's WW2 row certificate, at
`(α, r, p, η, h) = (2, 1, 1, .one, 0)` — `s = 2`, `m = 2`, `p = 1`, `2^α = 4`.

Everything except `hlinrow` is discharged: `1 ≤ α` by `norm_num`, the σ-column by the
coincidence, the hat's wild and tame columns by Rem. 5.4.  `hlinrow` is the linear copy's row at
σ-free offsets — the one `-b`-shaped input that remains, and the item the report names. -/
noncomputable def sqrtNeg10ProductRowCert {S : Type*} (ρ : S → AddMonoid.End V)
    (hV₂ : ∀ w : V, w + w = 0) (hwild : ∀ (i : Fin 3) (w : V), t.x i • w = w)
    (hτfpf : ∀ w : V, t.τ • w = w → w = 0) (hTodd : ∀ w : V, powOmega2 t.τ • w = w)
    (target : FoxRowNormalForm (Generator 2) S)
    (hσzero : target.row Generator.sigma = .zero)
    (hlinrow : ∀ a : Generator 2 → V, a Generator.sigma = 0 →
      foxD ⇑t a E E₂ (mpcLinW 2 1 1 .one 0) = target.toHom ρ a) :
    FoxRowCertificate ρ (foxDHom (A := V) ⇑t E E₂ sqrtNeg10ProductW) :=
  mpcProductRowCert (h := 0) t E E₂ ρ (α := 2) (by norm_num) 1 1 .one hV₂ hwild hτfpf hTodd
    target hσzero hlinrow

end SqrtNeg10

/-! ## §3 Self-replication cancellation, including every `T`-dependent central term

Draft Rem. 5.4's second-order half, and handoff item 2.  Three things had to meet: WMP-b's
cross-term killer, the **dual** half of the jet, and P4's central clause. -/

/-! ### The WW1↔WW3 bridge

`heisEvalZ` is `PWord.evalZ` (resolver-driven at every profinite node) while `foxEval` is
`PWord.evalFin` (which reads `ω₂` *intrinsically*, at the order of the lifted element).  They
agree exactly when the resolver is correct at the lift level — the standing discipline
`foxEval`'s own docstring states ("the resolvers `E`/`E₂` … must therefore be correct at the
lift level; orders may double").  `ResolverLifts` names that condition; it is a hypothesis,
not a theorem, and it is the *only* thing separating the two registers. -/

section Bridge

variable {X : Type*} {C : Type*} [Group C] {A : Type*} [AddCommGroup A] [DistribMulAction C A]

/-- **Resolver correctness at a lift level**: the resolver's `ω₂`-value acts on `G` as `ω₂`
itself does.  Satisfiable for any finite `G` by choosing `E omega2` in the right residue class;
`WordLift.orderOf_dvd_two_mul_orderOf_base` is the reason it has to be asked for separately at
each level rather than inherited from the base. -/
def ResolverLifts (E : Zhat → ℤ) (G : Type*) [Group G] : Prop :=
  ∀ p : G, p ^ E omega2 = powOmega2 p

/-- Under resolver correctness the two denotations coincide. -/
theorem evalZ_eq_evalFin_of_resolverLifts {G : Type*} [Group G] {E : Zhat → ℤ} {E₂ : ℤ_[2] → ℤ}
    (hres : ResolverLifts E G) (μ : X → G) :
    ∀ w : PWord X, PWord.evalZ μ E E₂ w = PWord.evalFin μ E E₂ w
  | .one => rfl
  | .gen _ => rfl
  | .mul u v => by
      rw [PWord.evalZ_mul, PWord.evalFin_mul, evalZ_eq_evalFin_of_resolverLifts hres μ u,
        evalZ_eq_evalFin_of_resolverLifts hres μ v]
  | .inv u => by
      rw [PWord.evalZ_inv, PWord.evalFin_inv, evalZ_eq_evalFin_of_resolverLifts hres μ u]
  | .conj u g => by
      rw [PWord.evalZ_conj, PWord.evalFin_conj, evalZ_eq_evalFin_of_resolverLifts hres μ u,
        evalZ_eq_evalFin_of_resolverLifts hres μ g]
  | .comm u v => by
      rw [PWord.evalZ_comm, PWord.evalFin_comm, evalZ_eq_evalFin_of_resolverLifts hres μ u,
        evalZ_eq_evalFin_of_resolverLifts hres μ v]
  | .zpow u k => by
      rw [PWord.evalZ_zpow, PWord.evalFin_zpow, evalZ_eq_evalFin_of_resolverLifts hres μ u]
  | .z2pow u z => by
      rw [PWord.evalZ_z2pow, PWord.evalFin_z2pow, evalZ_eq_evalFin_of_resolverLifts hres μ u]
  | .profPow u γ => by
      rw [PWord.evalZ_profPow, evalZ_eq_evalFin_of_resolverLifts hres μ u]
      rcases eq_or_ne γ omega2 with rfl | hγ
      · rw [PWord.evalFin_profPow_omega2, hres]
      · rw [PWord.evalFin_profPow_of_ne _ _ _ _ hγ]

/-- The **primal** projection `H(A) ⋊ C → WordLift A C`: it is a monoid hom because `mul_a`
and `mul_u` are the same rule. -/
def heisPrimal : HeisLift A C →* WordLift A C where
  toFun p := ⟨p.a, p.g⟩
  map_one' := rfl
  map_mul' _ _ := rfl

/-- The **dual** projection `H(A) ⋊ C → WordLift (ElemDual A) C`: likewise, because `mul_l` is
the same rule read on the contragredient module.  This is the observation that makes the dual
half of the jet a *corollary* of WMP-b's §5 rather than a re-derivation. -/
def heisDual : HeisLift A C →* WordLift (ElemDual A) C where
  toFun p := ⟨p.l, p.g⟩
  map_one' := rfl
  map_mul' _ _ := rfl

/-- The primal first jet **is** the Fox derivative at the primal offsets. -/
theorem heisEvalZ_a_eq_foxD {E : Zhat → ℤ} {E₂ : ℤ_[2] → ℤ}
    (hW : ResolverLifts E (WordLift A C)) (μ : X → C) (x : X → A) (y : X → ElemDual A)
    (w : PWord X) : (heisEvalZ μ x y E E₂ w).a = foxD μ x E E₂ w := by
  have h := PWord.map_evalZ (heisPrimal (A := A) (C := C)) (heisGen μ x y) E E₂ w
  have hu := congrArg WordLift.u h
  rw [foxD_def, foxEval_def, ← evalZ_eq_evalFin_of_resolverLifts hW]
  exact hu

/-- The **dual** first jet is the Fox derivative at the dual offsets — WMP-b delivered `.a = 0`,
and WW3's `heisJetZero_mul_z` consumes only `.l`, so this is the half that was missing. -/
theorem heisEvalZ_l_eq_foxD {E : Zhat → ℤ} {E₂ : ℤ_[2] → ℤ}
    (hW : ResolverLifts E (WordLift (ElemDual A) C)) (μ : X → C) (x : X → A)
    (y : X → ElemDual A) (w : PWord X) :
    (heisEvalZ μ x y E E₂ w).l = foxD μ y E E₂ w := by
  have h := PWord.map_evalZ (heisDual (A := A) (C := C)) (heisGen μ x y) E E₂ w
  have hu := congrArg WordLift.u h
  rw [foxD_def, foxEval_def, ← evalZ_eq_evalFin_of_resolverLifts hW]
  exact hu

end Bridge

/-! ### The ramified hypotheses, transferred to the dual module

`foxD_mpcHatW_ram` is stated for an arbitrary finite coefficient module, so the dual jet is the
*same theorem* at `A := ElemDual V` — provided the four ramified hypotheses transfer.  Three are
immediate; the fourth, fixed-point-freeness of `τ`, is the one with content: over a finite `V`
an injective `τ − 1` is surjective, and a functional killed by every `τ`-difference is killed by
everything. -/

section DualTransfer

variable {C : Type*} [Group C] {V : Type*} [AddCommGroup V] [Finite V] [DistribMulAction C V]

omit [Finite V] in
/-- Trivially-acting elements act trivially on the dual. -/
theorem elemDual_smul_eq_self {g : C} (hg : ∀ v : V, g • v = v) (lam : ElemDual V) :
    g • lam = lam := by
  refine ElemDual.ext fun v => ?_
  rw [ElemDual.smul_apply]
  have : g⁻¹ • v = v := by
    conv_lhs => rw [← hg v]
    rw [inv_smul_smul]
  rw [this]

/-- **Fixed-point-freeness transfers to the dual.**  If `g` fixes no nonzero vector then it
fixes no nonzero functional: `v ↦ g • v − v` is injective, hence surjective on a finite module,
and a `g`-invariant functional kills its whole image. -/
theorem elemDual_fpf {g : C} (hfpf : ∀ v : V, g • v = v → v = 0) (lam : ElemDual V)
    (hlam : g • lam = lam) : lam = 0 := by
  set f : V →+ V := (DistribSMul.toAddMonoidHom V g) - AddMonoidHom.id V with hf
  have hfapp : ∀ v : V, f v = g • v - v := fun v => rfl
  have hinj : Function.Injective f := by
    rw [injective_iff_map_eq_zero]
    intro v hv
    rw [hfapp, sub_eq_zero] at hv
    exact hfpf v hv
  have hsurj : Function.Surjective f := Finite.injective_iff_surjective.mp hinj
  refine ElemDual.ext fun v => ?_
  obtain ⟨u, rfl⟩ := hsurj v
  have h1 : lam (g⁻¹ • (g • u)) = lam (g • u) := by
    rw [← ElemDual.smul_apply g lam (g • u), hlam]
  rw [inv_smul_smul] at h1
  rw [hfapp, map_sub, ← h1, ElemDual.zero_apply, sub_self]

end DualTransfer

/-! ### The hat copy's full jet, and the cancellation -/

section Replication

variable {h : ℕ} {C : Type*} [Group C] [Finite C] {V : Type*} [AddCommGroup V] [Finite V]
  [DistribMulAction C V] (t : Marking (2 + 2 * h) C) (E : Zhat → ℤ) (E₂ : ℤ_[2] → ℤ)

/-- **The dual first Fox derivative of the hat copy vanishes.**  Not a re-derivation:
`foxD_mpcHatW_ram` is module-generic, so this is that theorem at `A := ElemDual V`, with the
four ramified hypotheses transferred by §3's two dual lemmas (`hV₂` is free — every `𝔽₂`-dual
functional kills itself). -/
theorem foxD_mpcHatW_ram_dual {α : ℕ} (hα : 1 ≤ α) (r pp : ℕ) (η : EtaDisplay)
    (y : Generator (2 + 2 * h) → ElemDual V) (hσ : y Generator.sigma = 0)
    (hwild : ∀ (i : Fin (2 + 2 * h + 1)) (w : V), t.x i • w = w)
    (hτfpf : ∀ w : V, t.τ • w = w → w = 0) (hTodd : ∀ w : V, powOmega2 t.τ • w = w) :
    foxD ⇑t y E E₂ (mpcHatW α r pp η h) = 0 :=
  foxD_mpcHatW_ram (V := ElemDual V) t E E₂ y hσ
    (fun i lam => elemDual_smul_eq_self (hwild i) lam)
    (fun lam hlam => elemDual_fpf hτfpf lam hlam)
    (fun lam => elemDual_smul_eq_self hTodd lam)
    hα r pp η (fun lam => ElemDual.add_self_eq_zero lam)

/-- **The hat copy is jet-zero** — both halves, hence WW3's membership.

WMP-b proved the primal half and noted that `heisJetZero_mul_z` consumes only the dual one;
neither alone gives the membership, and the membership is what every second-order consumer
(`heisJetZero_mul_right_jet`, `heisJetZero_sq_z`, `heisEvalZ_prodList_jetZero`) needs. -/
theorem heisJetZero_mpcHatW {α : ℕ} (hα : 1 ≤ α) (r pp : ℕ) (η : EtaDisplay)
    (x : Generator (2 + 2 * h) → V) (y : Generator (2 + 2 * h) → ElemDual V)
    (hσx : x Generator.sigma = 0) (hσy : y Generator.sigma = 0)
    (hWp : ResolverLifts E (WordLift V C)) (hWd : ResolverLifts E (WordLift (ElemDual V) C))
    (hV₂ : ∀ w : V, w + w = 0)
    (hwild : ∀ (i : Fin (2 + 2 * h + 1)) (w : V), t.x i • w = w)
    (hτfpf : ∀ w : V, t.τ • w = w → w = 0) (hTodd : ∀ w : V, powOmega2 t.τ • w = w) :
    heisEvalZ ⇑t x y E E₂ (mpcHatW α r pp η h) ∈ heisJetZero V C := by
  refine ⟨?_, ?_⟩
  · rw [heisEvalZ_a_eq_foxD hWp]
    exact foxD_mpcHatW_ram t E E₂ x hσx hwild hτfpf hTodd hα r pp η hV₂
  · rw [heisEvalZ_l_eq_foxD hWd]
    exact foxD_mpcHatW_ram_dual t E E₂ hα r pp η y hσy hwild hτfpf hTodd

/-- **The two copies' central values add — no cross term, `T`-dependent or otherwise.**

The cross term of the second-order product rule is `D^∨(R_lin)(val(R_lin)·D(R̂))`, and it dies on
the *primal* half of the hat's jet alone (WMP-b's `heisEvalZ_pair_z_of_hat_jetZero`, S1.5's
banked lemma (iii)(a)) — no module, no lift, no characteristic hypothesis, and in particular
nothing that could hide a `T`-dependent term: `T` enters only through `val(R_lin)`, which
multiplies zero. -/
theorem heisEvalZ_mpcProductW_z {α : ℕ} (hα : 1 ≤ α) (r pp : ℕ) (η : EtaDisplay)
    (x : Generator (2 + 2 * h) → V) (y : Generator (2 + 2 * h) → ElemDual V)
    (hσx : x Generator.sigma = 0) (hσy : y Generator.sigma = 0)
    (hWp : ResolverLifts E (WordLift V C)) (hWd : ResolverLifts E (WordLift (ElemDual V) C))
    (hV₂ : ∀ w : V, w + w = 0)
    (hwild : ∀ (i : Fin (2 + 2 * h + 1)) (w : V), t.x i • w = w)
    (hτfpf : ∀ w : V, t.τ • w = w → w = 0) (hTodd : ∀ w : V, powOmega2 t.τ • w = w) :
    (heisEvalZ ⇑t x y E E₂ (.mul (mpcLinW α r pp η h) (mpcHatW α r pp η h))).z
      = (heisEvalZ ⇑t x y E E₂ (mpcLinW α r pp η h)).z
        + (heisEvalZ ⇑t x y E E₂ (mpcHatW α r pp η h)).z :=
  heisEvalZ_pair_z_of_hat_jetZero ⇑t x y E E₂ _ _
    (heisJetZero_mpcHatW t E E₂ hα r pp η x y hσx hσy hWp hWd hV₂ hwild hτfpf hTodd)

/-- **P4's central clause, as a module hypothesis** — the shadow memo's own formulation.

The memo is explicit that this is "a module condition, checked exactly per module", *not*
something to re-measure: `value(δ_i)` and `value(x_i)` agree in lower, primal and dual (the
ramified clause, which is `P = 0`), and whether they also agree centrally is a property of the
module.  Its own table shows the clause **failing** on three of the four ramified simples while
the conclusion still holds, because the parity escape fires — so the honest Lean shape is a
hypothesis with two independent sufficient conditions, not a claim. -/
def CentralReplication {α : ℕ} (r pp : ℕ) (η : EtaDisplay)
    (x : Generator (2 + 2 * h) → V) (y : Generator (2 + 2 * h) → ElemDual V) : Prop :=
  (heisEvalZ ⇑t x y E E₂ (mpcHatW α r pp η h)).z
    = (heisEvalZ ⇑t x y E E₂ (mpcLinW α r pp η h)).z

/-- **The copies cancel in characteristic 2** — packet Rem. 5.4 / memo P5, assembled.

`central(uv) = central(u) + central(v) + λ(m_u, ū·m_v)`; P3 (the vanishing first jet, §3's
`heisJetZero_mpcHatW`) kills the cross term and P4 (the central clause) makes the two central
values equal, so the pair contributes `c + c = 0`.  What survives is the plus block — the word
identity `Q₊(c₀,c₁) = q(c₀) + b_q(c₀,c₁)`, not a finite-order interpolation. -/
theorem mpcCopiesCancel {α : ℕ} (hα : 1 ≤ α) (r pp : ℕ) (η : EtaDisplay)
    (x : Generator (2 + 2 * h) → V) (y : Generator (2 + 2 * h) → ElemDual V)
    (hσx : x Generator.sigma = 0) (hσy : y Generator.sigma = 0)
    (hWp : ResolverLifts E (WordLift V C)) (hWd : ResolverLifts E (WordLift (ElemDual V) C))
    (hV₂ : ∀ w : V, w + w = 0)
    (hwild : ∀ (i : Fin (2 + 2 * h + 1)) (w : V), t.x i • w = w)
    (hτfpf : ∀ w : V, t.τ • w = w → w = 0) (hTodd : ∀ w : V, powOmega2 t.τ • w = w)
    (hcentral : CentralReplication (α := α) t E E₂ r pp η x y) :
    (heisEvalZ ⇑t x y E E₂ (.mul (mpcLinW α r pp η h) (mpcHatW α r pp η h))).z = 0 := by
  rw [heisEvalZ_mpcProductW_z t E E₂ hα r pp η x y hσx hσy hWp hWd hV₂ hwild hτfpf hTodd,
    show (heisEvalZ ⇑t x y E E₂ (mpcHatW α r pp η h)).z
      = (heisEvalZ ⇑t x y E E₂ (mpcLinW α r pp η h)).z from hcentral,
    CharTwo.add_self_eq_zero]

/-! ### WW4 gap item 3, shadow half: the shadow contributes no affine shift

WW4 named the stated form and left the corollary unwritten ("the shadow contributes no primal or
dual offset when P3 holds, so it contributes no affine shift — but that is a corollary nobody
has written down").  Here it is, at *this* word rather than at an abstract jet-zero factor: the
whole first jet of the pair is the linear copy's, so the shift vector of packet Lem. 6.1 — which
is computed from the first jet — is unchanged, and only the central values move. -/

/-- **No affine shift from the shadow copy** (WW4's stated form, `heisJetZero_mul_right_jet`,
applied to `R̂^pc`). -/
theorem mpcShadow_no_affine_shift {α : ℕ} (hα : 1 ≤ α) (r pp : ℕ) (η : EtaDisplay)
    (x : Generator (2 + 2 * h) → V) (y : Generator (2 + 2 * h) → ElemDual V)
    (hσx : x Generator.sigma = 0) (hσy : y Generator.sigma = 0)
    (hWp : ResolverLifts E (WordLift V C)) (hWd : ResolverLifts E (WordLift (ElemDual V) C))
    (hV₂ : ∀ w : V, w + w = 0)
    (hwild : ∀ (i : Fin (2 + 2 * h + 1)) (w : V), t.x i • w = w)
    (hτfpf : ∀ w : V, t.τ • w = w → w = 0) (hTodd : ∀ w : V, powOmega2 t.τ • w = w) :
    (heisEvalZ ⇑t x y E E₂ (.mul (mpcLinW α r pp η h) (mpcHatW α r pp η h))).a
        = (heisEvalZ ⇑t x y E E₂ (mpcLinW α r pp η h)).a ∧
      (heisEvalZ ⇑t x y E E₂ (.mul (mpcLinW α r pp η h) (mpcHatW α r pp η h))).l
        = (heisEvalZ ⇑t x y E E₂ (mpcLinW α r pp η h)).l ∧
      (heisEvalZ ⇑t x y E E₂ (.mul (mpcLinW α r pp η h) (mpcHatW α r pp η h))).z
        = (heisEvalZ ⇑t x y E E₂ (mpcLinW α r pp η h)).z
          + (heisEvalZ ⇑t x y E E₂ (mpcHatW α r pp η h)).z :=
  heisJetZero_mul_right_jet _ _
    (heisJetZero_mpcHatW t E E₂ hα r pp η x y hσx hσy hWp hWd hV₂ hwild hτfpf hTodd)

end Replication

/-! ## §4 The Hessian/phase layer

`affinePhase` stays a **certificate input** (SD1 §6.3's row-5 satisfiability constraint), and
the constraint is honoured literally: every field below is instantiated from the frozen row's
endpoint polynomial plus a CoV `LinearEquiv` with its inverse witness, and nothing presupposes
the WC-Mpc analysis. -/

section Hessian

open GQ2.SectionSix GQ2.QuadraticFp2

variable {C V : Type} [Group C] [AddCommGroup V] [DistribMulAction C V]
  [Module (ZMod 2) V] [Fintype V] {q : V → ZMod 2} (dat : FactorSet C V)
  (hdat : IsEquivariantFactorSet q dat)

include hdat in
/-- **The procyclic-`M` phase cover**, WW4 gap items 1+2+6.

The endpoint is the plus block's: `D₀²[D₀,D₁]` is what survives the copies' cancellation and its
word value is `Q₊(c₀,c₁) = q(c₀) + b_q(c₀,c₁)` — a **plus form**, so `plusFormD` is the frozen
row's endpoint polynomial (item 1) and the identity map is its CoV (item 2).

⚠ Item 6 is honoured by *shape*, not by assertion: the diagonal is the abstract datum `d₀`, not
`q`.  On the four refinement-free `P = 0` modules the κ⁰-datum is `TwistedClass2Domain`-
normalized, so a certificate that hard-wired `diag := fun v ↦ dat.f v v` (the compact rows'
spelling) would be wrong here; taking `d₀` from the normalization is exactly S1.T's discipline,
and `nonsingular_plusFormD` is independent of `d₀`, so the twist cannot break nonsingularity. -/
noncomputable def mpcPhaseCover {d₀ : V → ZMod 2} (hd : IsQuadraticFp2 d₀)
    (hq : IsQuadraticFp2 q) (hns : Nonsingular q) {d : ℕ}
    (hcard : Fintype.card V = 2 ^ d) :
    PhaseCoverCertificate dat d₀ (plusFormD d₀ q) (AddMonoidHom.inl V V)
      (AddMonoidHom.inr V V) :=
  plusFormDPhaseCover dat hdat hd hq hns hcard

include hdat in
/-- **The procyclic-`M` Hessian certificate.**  The CoV is the identity (`LinearEquiv.refl`, its
inverse witness built into the structure, per SD1 §6.3), and `affinePhase` is `mpcPhaseCover` —
a certificate *input*, constructed, never derived. -/
noncomputable def mpcHessianCertificate {d₀ : V → ZMod 2} (hd : IsQuadraticFp2 d₀)
    (hq : IsQuadraticFp2 q) (hns : Nonsingular q) {d : ℕ}
    (hcard : Fintype.card V = 2 ^ d) :
    HessianCertificate dat d₀ (plusFormD d₀ q) (plusFormD d₀ q)
      (AddMonoidHom.inl V V) (AddMonoidHom.inr V V) where
  cov := LinearEquiv.refl (ZMod 2) (V × V)
  cov_eq := fun _ => rfl
  hq := isQuadraticFp2_plusFormD hd hq
  hns := nonsingular_plusFormD hd hq hns
  affinePhase := mpcPhaseCover dat hdat hd hq hns hcard

include hdat in
/-- The row's Gauss datum, read **through the certificate**: the endpoint's Gauss sum is the
phase cover's `G0`, and it is `+#V` — the `plusFormD` family's "one-op normal forms both
branches" behaviour, unchanged by the twist (`nonsingular_plusFormD` does not see `d₀`). -/
theorem mpcHessianCertificate_gaussSum {d₀ : V → ZMod 2} (hd : IsQuadraticFp2 d₀)
    (hq : IsQuadraticFp2 q) (hns : Nonsingular q) {d : ℕ}
    (hcard : Fintype.card V = 2 ^ d) :
    gaussSum (plusFormD d₀ q)
        = (mpcHessianCertificate dat hdat hd hq hns hcard).affinePhase.G0 ∧
      gaussSum (plusFormD d₀ q) = Fintype.card V :=
  ⟨(mpcHessianCertificate dat hdat hd hq hns hcard).endpoint_gaussSum,
    gaussSum_plusFormD hd hq hns⟩

/-- **WW4 gap item 5, named and left open.**

The word-side equation "evaluated Hessian `=` `Q`" — `hessRelZ` at the graph marking of
`kappa0Cocycle`, i.e. the `npc_cross_operators` analogue for the Mpc word, together with the
NpcJet↔WordCoh bridge.  It is wave-2 scope that no ticket owns; this definition states what it
would have to say so that a future ticket has a target, and so that no consumer mistakes the
constructed `affinePhase` for a discharged word-side equation.

⚠ **Epistemic status: an input, not a theorem of this file.** -/
def HessRelZTarget {X : Type*} (μ : X → SemiProd C V) (E : Zhat → ℤ) (E₂ : ℤ_[2] → ℤ)
    (w : PWord X) (Q : V × V → ZMod 2) (c₀ c₁ : V) : Prop :=
  hessRelZ μ (kappa0Cocycle dat hdat) E E₂ w = Q (c₀, c₁)

end Hessian

/-! ### The S4.5 block-order rider — a gate-D statement

`swap[E₂^pc.E₀₁^pc]` is DECIDED EQUAL, proof-grade (freeze row 5, addendum S4.5), and rider (i)
says any block-order statement WMP-c makes is a **gate-D statement, not a Hessian one**, because
`E₂^pc`'s second-order content is empty on the gate-E marking.  The decision note's §3.2
difference formula is

```
central(… E₀₁^pc E₂^pc …) + central(… E₂^pc E₀₁^pc …) = b(m_{E01}, m_{E2}),
    m_{E2} = 𝒪·(1 + P)c₂,   P = N_T
```

and on the gate-E marking `c₂ = 0`, so `m_{E2} = 0` and the difference vanishes.  Formalized in
WM0-c's `swapDifference_formula` discipline: the general two-slot formula with **opaque
offsets**, then the vanishing corollary as the syntactic instantiation at offset `0`, with the
operator `𝒪` a **bare function** carrying only `𝒪 0 = 0`.

⚠ **Rider (ii) is visible in the statement.**  The corollary's offset is `𝒪 0` because `x₂`
carries no primal letter; a formalization that gave the boundary generator a primal coordinate
would supply a nonzero `c₂`, `swapDifference_two_formula` would return a nonzero polar term, and
block order would become load-bearing again — exactly what the decision note says. -/

section OrderRider

open GQ2.QuadraticFp2

variable {C V : Type} [Group C] [AddCommGroup V] [DistribMulAction C V]
  {q : V → ZMod 2} (dat : FactorSet C V) (hdat : IsEquivariantFactorSet q dat)

include hdat in
/-- **The two-slot swap-difference formula.**  Charges are irrelevant — the four `z`'s cancel in
pairs — so only the `κ`-symmetrization survives, which is why the *difference* is proof-grade
where neither individual value is. -/
theorem swapDifference_two_formula (b₁ b₂ : V) (z₁ z₂ : ZMod 2) :
    WordCoh.CentExt.fib (c := kappa0Cocycle dat hdat)
        (hessSlice dat hdat b₁ z₁ * hessSlice dat hdat b₂ z₂)
      + WordCoh.CentExt.fib (c := kappa0Cocycle dat hdat)
        (hessSlice dat hdat b₂ z₂ * hessSlice dat hdat b₁ z₁)
      = polar q b₁ b₂ := by
  simp only [hessSlice_mul dat hdat, hessSlice_fib]
  linear_combination (norm := (ring_nf; simp [CharTwo.two_eq_zero])) (hdat.f_polar b₁ b₂)

include hdat in
/-- **S4.5: the block-order difference is zero on the gate-E marking** — because `x₂` carries no
primal letter, so the `E₂^pc` slot's offset `𝒪·(1+P)c₂` is `𝒪 0 = 0`.

This is a **gate-D statement**: `E₂^pc`'s second-order content is empty here, so nothing about
the Hessian endpoint is being claimed.  `𝒪` is a bare function (the orbit-norm operator), which
is why `hO0` has to be asked for — it has no `map_zero`. -/
theorem swapDifference_zero_of_no_primal_x2 (O : V → V) (hO0 : O 0 = 0)
    (hq : IsQuadraticFp2 q) (b₁ : V) (z₁ z₂ : ZMod 2) :
    WordCoh.CentExt.fib (c := kappa0Cocycle dat hdat)
        (hessSlice dat hdat b₁ z₁ * hessSlice dat hdat (O 0) z₂)
      + WordCoh.CentExt.fib (c := kappa0Cocycle dat hdat)
        (hessSlice dat hdat (O 0) z₂ * hessSlice dat hdat b₁ z₁)
      = 0 := by
  rw [swapDifference_two_formula dat hdat b₁ (O 0) z₁ z₂, hO0]
  simp [polar_zero_right q hq]

end OrderRider

/-! ## §5 The `E₀₁^pc` epistemics

Three statements, three statuses.  The two theorems are below; the third row of the module
docstring's table is a **citation**, and this section does not turn it into a Lean claim. -/

section E01

variable {h : ℕ} {C : Type*} [Group C] [Finite C] {V : Type*} [AddCommGroup V] [Finite V]
  [DistribMulAction C V] (t : Marking (2 + 2 * h) C) (E : Zhat → ℤ) (E₂ : ℤ_[2] → ℤ)
  (a : Generator (2 + 2 * h) → V)

/-- **Gate D cannot see `E₀₁^pc`** — the pair-level form, and the operative half of the freeze's
finding.

`Sh_M` fixes `E₀₁^pc` verbatim (it is a word in `δ₀, δ₁, σ₂` alone), so the block occurs
*identically* in both copies; the linear copy's value acts trivially on the block's row, so the
two contributions add rather than compose, and over `𝔽₂` they cancel.  A first-order argument
therefore cannot distinguish the word that contains the block from the word that does not: the
shadow puts the identical contribution back.

⚠ This says gate D is **silent**, not that `E₀₁^pc` is superfluous — see the module docstring's
table.  The positive justification is second-order and is cited, not proved. -/
theorem foxD_e01_pair_eq_zero (η : EtaDisplay) (aa bb : ℕ) (hV₂ : ∀ w : V, w + w = 0)
    (hwild : ∀ (i : Fin (2 + 2 * h + 1)) (w : V), t.x i • w = w)
    (hTodd : ∀ w : V, powOmega2 t.τ • w = w) :
    foxD ⇑t a E E₂ (.mul (e01W h aa bb) (inlineM h η (shM (e01M aa bb)))) = 0 := by
  rw [foxD_mul, foxD_e01_reproduced_by_shadow t E E₂ a η aa bb,
    mem_trivAct.mp (trivAct_e01W t E E₂ hwild hTodd aa bb)]
  exact hV₂ _

/-- **The shape of the `E₀₁^pc` second-order justification** — recorded, deliberately *not*
proved.

Freeze row 5: `E₀₁^pc`'s justification is second-order only, and specifically the **exact gate-F
refutation on the fifth-root module**.  S4.4's finding is that dropping the block passes gates
A–E-scalar and dies at gate F.  Gate F is an `𝔽₁₆`-module computation on the *second*-order
data, which is a different object from anything WMP-b or this ticket built; the witness a Lean
proof would need is a module together with a second-order discriminator separating the two
words.  This definition names that shape so a future ticket has a target, and so that nobody
mistakes `foxD_e01_pair_eq_zero` (gate D is silent) for a justification.

⚠ **Epistemic status: measurement, cited (S4.4 / freeze row 5), not a theorem of this file.** -/
def E01SecondOrderWitness {α : ℕ} (r pp : ℕ) (η : EtaDisplay)
    (x : Generator (2 + 2 * h) → V) (y : Generator (2 + 2 * h) → ElemDual V)
    (wNoE01 : PWord (Generator (2 + 2 * h))) : Prop :=
  (heisEvalZ ⇑t x y E E₂ (mpcW α r pp η h)).z ≠ (heisEvalZ ⇑t x y E E₂ wNoE01).z

end E01

end GQ2.Dyadic.Certificates.MProcyclic
