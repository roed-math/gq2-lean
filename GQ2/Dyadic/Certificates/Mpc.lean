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

(`foxDHom_mpcProductW_eq_sigmaKill`), from exactly two WMP-b inputs and nothing else: §5's
`foxD_mpcHatW_ram` (the hat's wild/tame columns vanish) and §4's `foxColumn_sigma_mul_eq_zero`
(the pair's σ-column vanishes, by the coincidence, without either factor vanishing).

⚠ **The certificate is stated as a transport, and that is deliberate.**  A `FoxRowCertificate`
for the pair is produced from one for the linear copy whose target has a zero σ-entry
(`productRowCertOfLin`), because the linear copy's own closed-form row at general `(α, r, p)` is
a `-b` computation that WMP-b did not do and this ticket does not own.  What *is* proved here is
that the transport is sound and that its hypothesis is exactly the shape both sibling lanes'
frozen rows already have (`mCompactWildRow` and `npcWildRow` both carry `.sigma => .zero`) —
so the pair's row is the linear row **in the register the freeze uses**, and the σ-entry that
would otherwise be unavailable is the one entry the pair kills.  The `√−10` instance
(`sqrtNeg10ProductRowCertOfLin`) is the `(α,r,p,η,h) = (2,1,1,.one,0)` specialization, pinned
against merge gate 9's digest by `mpcW`-identity.

## §3 Self-replication cancellation, including every `T`-dependent central term (item 2)

Draft Rem. 5.4's second-order half.  Three things had to meet:

1. the **cross term** — `heisEvalZ_pair_z_of_hat_jetZero`, WMP-b's ready killer, consuming the
   *primal* half `p.a = 0`;
2. the **dual jet** `p.l = 0` for the hat copy — WMP-b delivered only the primal half, and
   WW3's `heisJetZero_mul_z` consumes only `.l`, so neither half alone gives the membership.
   Proved here as `heisEvalZ_mpcHatW_l_eq_zero` by the *same* structural route as the primal
   one, over the dual module `ElemDual V`: the dual first jet of a `HeisLift` value is a Fox
   derivative of the dual marking, so §5's theorem applies verbatim once the ramified
   hypotheses are read in `ElemDual V`.  The membership is `heisJetZero_mpcHatW`.
3. **P4's central clause**, which is a *module hypothesis*, not something to re-measure.  The
   shadow memo is explicit ("P4's hypothesis is a module condition, checked exactly per module
   here"), and its own table shows the clause **failing** on three of the four ramified simples
   while the conclusion still holds — because the parity escape fires.  Discharged here for
   ramified simples in the memo's own form: `centralReplication` is carried as the hypothesis
   `hcentral`, and `mpcCopiesCancel_of_replication` is the char-2 conclusion.  The escape route
   is recorded too (`shadowOccurrenceParity_even`, the `A²[A,B]` shape's two even parities), so
   a consumer that cannot check the central clause can use the parity clause instead.

## §4 `affinePhase` (item 3) and the S4.5 block-order rider

`affinePhase` stays a **certificate input** — SD1 §6.3's row-5 satisfiability constraint is
binding, and the fields must be instantiable from the frozen row's endpoint polynomial, a CoV
`LinearEquiv` with inverse witness, and per-χ shift vectors, with nothing presupposing the
WC-Mpc analysis.  What this ticket adds against WW4's six-item gap list:

* item 4 (the σ-column coincidence lemma) — already banked by WMP-b;
* item 3's shadow half — **`mpcShadow_no_affine_shift`**, the corollary WW4 named but left
  unwritten, in WW4's own stated form (against `heisJetZero`, via `heisJetZero_mul_right_jet`),
  now applied to *this* word's hat copy rather than to an abstract jet-zero factor;
* items 1, 2, 6 — the endpoint polynomial and its CoV, **constructible**: the plus block
  `D₀²[D₀,D₁]` is what survives the cancellation, its word value is `Q₊(c₀,c₁) = q(c₀) +
  b_q(c₀,c₁)` (WMP-a's word identity, §5 here), and that is a `plusFormD` endpoint — so
  `mpcPhaseCover` and `mpcHessianCertificate` are built from WW4's `plusFormDPhaseCover` with
  the twisted κ⁰ diagonal, honouring item 6's `TwistedClass2Domain` normalization by taking
  `diag` from `dat` rather than from `q`;
* item 5 (the word-side `hessRelZ` equation at the graph marking) — **remains an input.**  It
  is the `npc_cross_operators` analogue and needs the NpcJet↔WordCoh bridge, which is wave-2
  scope that no ticket owns; the file states what it would have to say
  (`HessRelZTarget`) and does not pretend to it.

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
| **theorem, here** | at first order the shadow reproduces `E₀₁^pc`'s entire contribution, so **gate D cannot see it** — dropping it changes no Fox row | `foxD_mpcProductW_e01_invisible` |
| **theorem, here** | the block-order difference vanishes on the gate-E marking (S4.5) | `swapDifference_zero_of_no_primal_x2` |
| **NOT proved here; cited** | the *positive* justification — gate F fails on the fifth-root module without `E₀₁^pc` | S4.4 measurement, `docs/dyadic/tickets.md` freeze row 5 |

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

**Hoist candidates** (beside WMP-b's seven): `ActsAsPow` and its five closure lemmas,
`sigmaKill`, and `foxD_of_sigma_free_eq` — all lane-generic, none mentions this word.

**Audited axiom state**: every named declaration of this file depends on a subset of
`[propext, Classical.choice, Quot.sound]` (scratch audit over the full declaration list; not
committed).  Zero `sorryAx`, zero `native_decide` — kernel `decide` only — so the census is
untouched at eleven.
-/

namespace GQ2.Dyadic.Certificates.MProcyclic

open GQ2.FoxH GQ2.Dyadic.Words.Mpc

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

end GQ2.Dyadic.Certificates.MProcyclic
